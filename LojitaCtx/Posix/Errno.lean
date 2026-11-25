namespace LojitaCtx.Posix

inductive Errno where
  | ENOENT | EINTR | EIO | EBADF | EAGAIN | EACCES | EEXIST | EXDEV
  | ENOTDIR | EISDIR | EINVAL | EMFILE | ENOSPC | ESPIPE | EROFS
  | EPIPE | ENAMETOOLONG | ENOTEMPTY | ELOOP | ECONNREFUSED | ETIMEDOUT
  | EPERM | ENOTTY | ENXIO | ERANGE | EOPNOTSUPP | ENOTCONN | EISCONN | ENOTSOCK | other (number : Nat)
  deriving Repr, Inhabited

def Errno.ctorIdx : Errno → Nat
  | .ENOENT => 0
  | .EINTR => 1
  | .EIO => 2
  | .EBADF => 3
  | .EAGAIN => 4
  | .EACCES => 5
  | .EEXIST => 6
  | .EXDEV => 7
  | .ENOTDIR => 8
  | .EISDIR => 9
  | .EINVAL => 10
  | .EMFILE => 11
  | .ENOSPC => 12
  | .ESPIPE => 13
  | .EROFS => 14
  | .EPIPE => 15
  | .ENAMETOOLONG => 16
  | .ENOTEMPTY => 17
  | .ELOOP => 18
  | .ECONNREFUSED => 19
  | .ETIMEDOUT => 20
  | .EPERM => 21
  | .ENOTTY => 22
  | .ENXIO => 23
  | .ERANGE => 24
  | .EOPNOTSUPP => 25
  | .ENOTCONN => 26 | .EISCONN => 27 | .ENOTSOCK => 28 | .other _ => 29

private def Errno.key (e : Errno) : Nat ⊕ Nat :=
  match e with
  | .other n => .inr n
  | _ => .inl e.ctorIdx

private def Errno.ofKey : (Nat ⊕ Nat) → Errno
  | .inr n => .other n
  | .inl k => match k with
    | 0 => .ENOENT
    | 1 => .EINTR
    | 2 => .EIO
    | 3 => .EBADF
    | 4 => .EAGAIN
    | 5 => .EACCES
    | 6 => .EEXIST
    | 7 => .EXDEV
    | 8 => .ENOTDIR
    | 9 => .EISDIR
    | 10 => .EINVAL
    | 11 => .EMFILE
    | 12 => .ENOSPC
    | 13 => .ESPIPE
    | 14 => .EROFS
    | 15 => .EPIPE
    | 16 => .ENAMETOOLONG
    | 17 => .ENOTEMPTY
    | 18 => .ELOOP
    | 19 => .ECONNREFUSED
    | 20 => .ETIMEDOUT
    | 21 => .EPERM
    | 22 => .ENOTTY
    | 23 => .ENXIO
    | 24 => .ERANGE
    | 25 => .EOPNOTSUPP
    | 26 => .ENOTCONN
    | 27 => .EISCONN
    | 28 => .ENOTSOCK
    | _ => .EIO

private theorem Errno.ofKey_key (e : Errno) : ofKey e.key = e := by cases e <;> rfl

instance : DecidableEq Errno := fun a b =>
  decidable_of_iff (a.key = b.key) ⟨fun h => by simpa only [Errno.ofKey_key] using congrArg Errno.ofKey h, congrArg Errno.key⟩

def Errno.code : Errno → Nat
  | .EPERM => 1 | .ENOENT => 2 | .EINTR => 4 | .EIO => 5 | .ENXIO => 6
  | .EBADF => 9 | .EAGAIN => 11 | .EACCES => 13 | .EEXIST => 17 | .EXDEV => 18
  | .ENOTDIR => 20 | .EISDIR => 21 | .EINVAL => 22 | .EMFILE => 24 | .ENOTTY => 25
  | .ENOSPC => 28 | .ESPIPE => 29 | .EROFS => 30 | .EPIPE => 32 | .ERANGE => 34
  | .ENAMETOOLONG => 36 | .ENOTEMPTY => 39 | .ELOOP => 40 | .EOPNOTSUPP => 95
  | .ENOTSOCK => 88 | .ENOTCONN => 107 | .EISCONN => 106
  | .ETIMEDOUT => 110 | .ECONNREFUSED => 111
  | .other n => n

def Errno.decode : Nat → Errno
  | 1 => .EPERM
  | 2 => .ENOENT
  | 4 => .EINTR
  | 5 => .EIO
  | 6 => .ENXIO
  | 9 => .EBADF
  | 11 => .EAGAIN
  | 13 => .EACCES
  | 17 => .EEXIST
  | 18 => .EXDEV
  | 20 => .ENOTDIR
  | 21 => .EISDIR
  | 22 => .EINVAL
  | 24 => .EMFILE
  | 25 => .ENOTTY
  | 28 => .ENOSPC
  | 29 => .ESPIPE
  | 30 => .EROFS
  | 32 => .EPIPE
  | 34 => .ERANGE
  | 36 => .ENAMETOOLONG
  | 39 => .ENOTEMPTY
  | 40 => .ELOOP
  | 95 => .EOPNOTSUPP
  | 88 => .ENOTSOCK
  | 107 => .ENOTCONN
  | 106 => .EISCONN
  | 110 => .ETIMEDOUT
  | 111 => .ECONNREFUSED
  | n => .other n

abbrev Errno.EWOULDBLOCK := Errno.EAGAIN

end LojitaCtx.Posix
