"""Exercise signals against the verified POSIX program's real Linux syscalls."""
import contextlib
import fcntl
import os
from pathlib import Path
import pty
import select
import signal
import subprocess
import sys
import termios
import time

binary = Path(sys.argv[1]).resolve()
INT, WINCH = signal.SIGINT, signal.SIGWINCH
environment = {**os.environ, "LEAN_STACK_SIZE_KB": "8192", "LEAN_NUM_THREADS": "3",
               "LEAN_MAIN_USE_THREAD": "1"}

def byte(child, expected):
    if not select.select([child.stdout], [], [], 4)[0]:
        raise AssertionError(f"{child.args} timed out waiting for {expected!r}")
    got = child.stdout.read(1)
    assert expected == got, (child.args, expected, got, child.poll())

def syscall(child, number):
    # x86-64 /proc identifies the syscall without a timing guess or signal handler
    # instrumentation. The parent reads only the thread list of its own process.
    deadline = time.monotonic()+2
    tasks = Path(f"/proc/{child.pid}/task")
    while time.monotonic() < deadline:
        assert child.poll() is None, (child.args,child.returncode)
        tids=list(tasks.iterdir())
        for t in tids:
            try:
                state=(t/"syscall").read_text().split()
                if state and state[0] == str(number) and (number != 0 or int(state[1],16)==0):
                    mask=lambda s: 1 << (s-1)
                    blocked=mask(INT)|mask(WINCH)
                    assert len(tids)>1, "expected actual Lean runtime workers"
                    for worker in tids:
                        if worker==t: continue
                        entry=(worker/"status").read_text().split("SigBlk:")[1].split()[0]
                        assert int(entry,16)&blocked == blocked, (worker,entry)
                    return
            except (FileNotFoundError,ProcessLookupError):
                continue
        time.sleep(.001)
    raise AssertionError(f"{child.args} did not enter syscall {number}")

@contextlib.contextmanager
def started(mode, terminal=False, ignored=False, masked=False):
    master,slave=pty.openpty() if terminal else (None,None)
    def child_setup():
        if terminal:
            os.setsid()
            fcntl.ioctl(slave,termios.TIOCSCTTY,0)
            os.tcsetpgrp(slave,os.getpgrp())
        signal.signal(INT,signal.SIG_IGN if ignored else signal.SIG_DFL)
        signal.pthread_sigmask(signal.SIG_BLOCK if masked else signal.SIG_UNBLOCK,{INT})
    try:
        p=subprocess.Popen([binary,mode],stdin=slave if terminal else subprocess.PIPE,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,env=environment,
                           preexec_fn=child_setup)
        try:
            byte(p,b"R")
            yield p,master
        finally:
            if p.poll() is None: p.kill()
            p.communicate(timeout=2)
    finally:
        if terminal:
            os.close(slave)
            os.close(master)

for sig in (INT,WINCH):
    with started("catch") as (p,_):
        syscall(p,271)
        os.kill(p.pid,sig)
        byte(p,b"E")
        assert p.wait(timeout=2)==0

# Send the actual foreground terminal line discipline's VINTR byte.
for catch in (True,False):
    with started("catch" if catch else "plain",terminal=True) as (p,master):
        syscall(p,271)
        assert os.write(master,b"\x03")==1
        if catch: byte(p,b"E")
        assert p.wait(timeout=2)==(0 if catch else -INT)

for mode,waiting in (("pending",0),("defer",271)):
    with started(mode) as (p,_):
        syscall(p,waiting)
        os.kill(p.pid,WINCH)
        if mode=="pending":
            p.stdin.write(b"x")
            p.stdin.flush()
        byte(p,b"E")
        assert p.wait(timeout=2)==0

for mode,ignored,masked in (("restore",False,False),("timeout",False,False),
                            ("ignored",True,False),("restore",False,True)):
    with started(mode,ignored=ignored,masked=masked) as (p,_):
        if mode=="timeout": byte(p,b"T")
        else:
            syscall(p,271)
            os.kill(p.pid,WINCH)
            byte(p,b"E")
        syscall(p,0)
        os.kill(p.pid,INT)
        if ignored or masked:
            p.stdin.write(b"x")
            p.stdin.flush()
            assert p.wait(timeout=2)==0
        else:
            assert p.wait(timeout=2)==-INT

print("Verified ELF passed SIGINT, real terminal Ctrl+C, pending SIGWINCH, worker masks and inherited signal restoration.")
