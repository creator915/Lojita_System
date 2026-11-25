import LojitaCtx.Posix.Kernel.OpenOffsets

namespace LojitaCtx.Posix

/-- Descriptor identity, allocation, offsets, and byte visibility at the syscall boundary. -/
theorem dup2_shared_vs_openat_isolated :
    (∀ {m n : Machine} {a b id : Nat} (src : Holds m a id) {sl : StepSlice}
    (success : stepSyscall m sl (.dup2 a b) = (.ok b,n)),
    Holds n a id ∧ Holds n b id) ∧
    (∀ {m n : Machine} {a b id ino size : Nat} {d : OpenFileDesc}
    (src : Holds m a id) (dst : Holds m b id) (desc : m.kernel.ofds[id]? = some d)
    (reg : d.target = .inode ino) (readable : d.flags.access ≠ .writeOnly)
    (sl nextSlice : StepSlice) (out : Bytes)
    (read : stepSyscall m sl (.read a size) = (.ok out.toByteArray,n)),
    (stepSyscall n nextSlice (.lseek b 0 .cur)).1 = .ok (d.offset+out.length)) ∧
    (∀ {m n : Machine} {sl : StepSlice} {fd mode : Nat}
    {dir : DirFd} {path : Bytes} {f : OpenFlags}
    (h : stepSyscall m sl (.openat dir path f mode) = (.ok fd,n)),
    ∃ id, Holds n fd id ∧ (∀ old ∈ m.kernel.ofds, id ≠ old) ∧
      ∀ other j, Holds m other j → Holds n other j) ∧
    (∀ {m n : Machine} {a b i j ino : Nat} {writer reader : OpenFileDesc}
    (src : Holds m a i) (dst : Holds m b j) (distinct : i ≠ j)
    (w : m.kernel.ofds[i]? = some writer) (r : m.kernel.ofds[j]? = some reader)
    (wreg : writer.target = .inode ino) (rreg : reader.target = .inode ino)
    (writable : writer.flags.access ≠ .readOnly) (readable : reader.flags.access ≠ .writeOnly)
    (appendOff : writer.flags.append = false) (offset : reader.offset = writer.offset)
    {old : Inode} {before : ByteArray} (node : m.kernel.vfs.node ino = .ok old)
    (regular : old.payload = .reg before) (linked : old.nlink ≠ 0)
    (data : Bytes) (nonempty : data ≠ []) (sl rd : StepSlice)
    (awake : sl.intrBefore = false) (rdAwake : rd.intrBefore = false)
    (fits : (data.take (max 1 sl.maxBytes)).length ≤ max 1 rd.maxBytes)
    (success : stepSyscall m sl (.write a data.toByteArray) = (.ok (data.take (max 1 sl.maxBytes)).length,n)),
    let bs := data.take (max 1 sl.maxBytes)
    (stepSyscall n rd (.lseek b 0 .cur)).1 = .ok reader.offset ∧
    (stepSyscall n rd (.read b bs.length)).1 = .ok bs.toByteArray) :=
  ⟨@dup2_aliases, @read_alias_seek, @open_new_description, @independent_write_read⟩

end LojitaCtx.Posix
