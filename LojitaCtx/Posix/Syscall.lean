import LojitaCtx.Posix.Tty

namespace LojitaCtx.Posix

abbrev DirFd := Option Fd
structure PollReq where
  fd : Fd
  events : Nat
  deriving Repr, DecidableEq, Inhabited

inductive Whence where | set | cur | «end»
  deriving Repr, Inhabited

def Whence.ctorIdx : Whence → Nat
  | .set => 0 | .cur => 1 | .end => 2
deriving instance BEq for Whence

inductive SysOp where
  | read (fd count : Nat)
  | write (fd : Fd) (data : Bytes)
  | pread (fd count off : Nat)
  | pwrite (fd : Fd) (data : Bytes) (off : Nat)
  | lseek (fd : Fd) (offset : Int) (whence : Whence)
  | close (fd : Fd)
  | dup2 (src dst : Fd)
  | setNonblock (fd : Fd) (on : Bool)
  | setCloexec (fd : Fd) (on : Bool)
  | pipe2 (nonblock cloexec : Bool)
  | ppoll (reqs : List PollReq) (timeoutMs : Option Nat) (catchSigs : Bool)
  | fstat (fd : Fd)
  | openat (dir : DirFd) (path : Bytes) (flags : OpenFlags) (mode : FileMode)
  | mkdirat (dir : DirFd) (path : Bytes) (mode : FileMode)
  | unlinkat (dir : DirFd) (path : Bytes) (removedir : Bool)
  | symlinkat (target : Bytes) (dir : DirFd) (path : Bytes)
  | renameat (oldDir : DirFd) (oldPath : Bytes) (newDir : DirFd) (newPath : Bytes)
  | readlinkat (dir : DirFd) (path : Bytes)
  | fstatat (dir : DirFd) (path : Bytes) (follow : Bool)
  | chdir (path : Bytes)
  | getcwd
  | tcgetattr (fd : Fd)
  | tcsetattr (fd : Fd) (attrs : Termios)
  | getWinsize (fd : Fd)
  | setWinsize (fd : Fd) (size : Winsize)
  | isatty (fd : Fd)
  | socketStream (nonblock cloexec : Bool)
  | connectLoopback (fd : Fd) (port : Nat)
  | shutdown (fd : Fd) (readEnd writeEnd : Bool)
  | clockGettime
  | nanosleep (nanoseconds : Nat)
  | getArgs
  | lookupEnv (name : Bytes)
  deriving Repr

def SysOp.ctorIdx : SysOp → Nat
  | .read .. => 0
  | .write .. => 1
  | .pread .. => 2
  | .pwrite .. => 3
  | .lseek .. => 4
  | .close .. => 5
  | .dup2 .. => 6
  | .setNonblock .. => 7
  | .setCloexec .. => 8
  | .pipe2 .. => 9
  | .ppoll .. => 10
  | .fstat .. => 11
  | .openat .. => 12
  | .mkdirat .. => 13
  | .unlinkat .. => 14
  | .symlinkat .. => 15
  | .renameat .. => 16
  | .readlinkat .. => 17
  | .fstatat .. => 18
  | .chdir .. => 19
  | .getcwd => 20
  | .tcgetattr .. => 21
  | .tcsetattr .. => 22
  | .getWinsize .. => 23
  | .setWinsize .. => 24
  | .isatty .. => 25
  | .socketStream .. => 26
  | .connectLoopback .. => 27
  | .shutdown .. => 28
  | .clockGettime => 29
  | .nanosleep .. => 30
  | .getArgs => 31
  | .lookupEnv .. => 32

set_option deriving.beq.linear_construction_threshold 100 in
deriving instance BEq for SysOp


def SysOp.cap : SysOp → Cap
  | .openat .. | .mkdirat .. | .unlinkat .. | .symlinkat .. | .renameat .. | .readlinkat ..
  | .fstatat .. | .chdir .. | .getcwd => .fsPathCap
  | .tcgetattr .. | .tcsetattr .. | .getWinsize .. | .setWinsize .. | .isatty .. => .ttyCap
  | .socketStream .. | .connectLoopback .. | .shutdown .. => .netCap
  | .clockGettime | .nanosleep .. => .clockCap
  | .getArgs | .lookupEnv .. => .envCap
  | _ => .fdIoCap

inductive ResultKind where
  | unit | nat | pair | bytes | masks | stat | tty | size | boolean | argv | env

def ResultKind.ctorIdx : ResultKind → Nat
  | .unit => 0 | .nat => 1 | .pair => 2 | .bytes => 3 | .masks => 4 | .stat => 5
  | .tty => 6 | .size => 7 | .boolean => 8 | .argv => 9 | .env => 10

deriving instance DecidableEq for ResultKind

def ResultKind.denote : ResultKind → Type
  | .unit => Unit | .nat => Nat | .pair => Fd × Fd | .bytes => Bytes
  | .masks => List Nat | .stat => StatObs | .tty => Termios | .size => Winsize
  | .boolean => Bool | .argv => List Bytes | .env => Option Bytes

def SysOp.kind : SysOp → ResultKind
  | .read .. | .pread .. | .getcwd | .readlinkat .. => .bytes
  | .write .. | .pwrite .. | .lseek .. | .dup2 .. | .openat .. | .socketStream .. | .clockGettime => .nat
  | .pipe2 .. => .pair | .ppoll .. => .masks | .isatty .. => .boolean
  | .fstat .. | .fstatat .. => .stat | .tcgetattr .. => .tty | .getWinsize .. => .size
  | .getArgs => .argv | .lookupEnv .. => .env
  | _ => .unit

abbrev SysOp.Result (op : SysOp) := op.kind.denote

end LojitaCtx.Posix
