#!/usr/bin/python3
"""Independent real-process fixtures, deliberately unaware of the relay protocol.

All interaction is through OS pipes, /dev/tty, monotonic time and real signals.
The corresponding transition systems and expectations are written in Agda.
"""
import os
import select
import signal
import struct
import sys
import time
import fcntl
import termios

tty = os.open('/dev/tty', os.O_RDWR)
scenario = sys.argv[1]
assert os.tcgetpgrp(tty) == os.getpgrp()
assert [os.isatty(i) for i in range(3)] == ([True] * 3 if scenario == 'alltty' else [False] * 3)


def emit(fd, data):
    while data:
        n = os.write(fd, data)
        data = data[n:]


if scenario == 'pipe':
    emit(tty, b'ready\n')
    emit(2, b'error-channel\n')
    candidates, pending, query = [], b'', b''
    sources = [0, tty]
    while True:
        readable, _, _ = select.select(sources, [], [])
        for fd in readable:
            chunk = os.read(fd, 4096)
            if fd == 0:
                if not chunk:
                    sources.remove(0)
                    emit(tty, b'eof\n')
                pending += chunk
                while b'\n' in pending:
                    line, pending = pending.split(b'\n', 1)
                    candidates.append(line)
                    emit(tty, b'candidate:' + line + b'\n')
            else:
                for key in chunk:
                    if key == 13:
                        chosen = next((c for c in candidates if c.startswith(query)), b'')
                        emit(tty, b'chosen\n')
                        emit(1, chosen + b'\n')
                        emit(2, b'done\n')
                        sys.exit(0)
                    query += bytes([key])
                    emit(tty, b'key:' + bytes([key]) + b'\n')

elif scenario == 'timer':
    deadline = None
    fired = False

    def interrupt(sig, frame):
        emit(tty, b'bye\n')
        sys.exit(0)

    signal.signal(signal.SIGINT, interrupt)
    emit(tty, b'ready\n')
    pending = b''
    while True:
        wait = None if deadline is None else max(0, deadline - time.monotonic())
        readable, _, _ = select.select([0, tty], [], [], wait)
        if deadline is not None and time.monotonic() >= deadline:
            deadline = None
            fired = True
            emit(tty, b'timeout\n')
        for fd in readable:
            chunk = os.read(fd, 4096)
            if fd == 0:
                if not chunk:
                    sys.exit(3)
                pending += chunk
                while b'\n' in pending:
                    line, pending = pending.split(b'\n', 1)
                    assert line == b'arm'
                    deadline, fired = time.monotonic() + 2.0, False
                    emit(tty, b'armed\n')
            else:
                for _ in chunk:
                    emit(tty, b'late\n' if fired else b'preempt\n')
                    deadline = None

elif scenario == 'ansi':
    emit(tty, b'ready\n')
    for line in sys.stdin.buffer:
        if line == b'draw\n':
            emit(tty, b'\x1b[2J\x1b[Hstale\x1b[2K\rOK\x1b[2;4H!\x1b[1D?'
                      b'\x1b[1A\x1b[2C#\x1b[2;1frow\x1b[1G>\x1b[0m')
        elif line == b'quit\n':
            sys.exit(0)
        else:
            sys.exit(4)

elif scenario == 'signals':
    def size(sig=None, frame=None):
        rows, cols, _, _ = struct.unpack('HHHH', fcntl.ioctl(tty, termios.TIOCGWINSZ, bytes(8)))
        emit(tty, f'size:{rows}x{cols}\n'.encode('ascii'))

    def interrupt(sig, frame):
        emit(tty, b'interrupt\n')
        emit(2, b'handled\n')
        sys.exit(0)

    signal.signal(signal.SIGWINCH, size)
    signal.signal(signal.SIGINT, interrupt)
    size()
    while True:
        signal.pause()

elif scenario == 'files':
    expected = {'TERM': 'xterm-256color', 'LC_ALL': 'C.UTF-8', 'DECLARED': 'visible'}
    assert dict(os.environ) == expected, repr(dict(os.environ))
    emit(1, b'env:clean:visible\n')
    with open('nested/note.txt', 'r+', encoding='utf-8') as f:
        previous = f.read()
        f.seek(0)
        f.write(previous + '|updated\n')
        f.truncate()
    emit(2, b'file:written\n')
    emit(tty, b'owned\n')
    # stop must terminate a still-live session before recovering this tree.
    while True:
        signal.pause()

elif scenario == 'binary':
    emit(tty, b'ready\n')
    data = b''
    while len(data) < 256:
        data += os.read(0, 256 - len(data))
    assert data == bytes(range(256))
    emit(tty, data)
    emit(1, data)
    emit(2, data)
    data = b''
    while len(data) < 256:
        data += os.read(tty, 256 - len(data))
    assert data == bytes(range(256))
    emit(tty, data)
    sys.exit(0)

elif scenario == 'alltty':
    emit(1, b'stdout\n')
    emit(2, b'stderr\n')
    emit(tty, b'tty\n')
    assert os.read(0, 1) == b'x'
    emit(tty, b'input\n')
    sys.exit(7)

else:
    raise RuntimeError(scenario)
