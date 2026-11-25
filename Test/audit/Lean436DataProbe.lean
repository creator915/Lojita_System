import LojitaCtx.Posix.Vfs.FileBytes
import Std.Data.TreeMap
open LojitaCtx.Posix

@[noinline] def primitiveChecks (n : Nat) : Bool := Id.run do
  let b := n.toUInt8
  let raw := ([0,255,128] : Bytes).toByteArray
  if raw != (ByteArray.mk #[0,255,128]) || raw == (ByteArray.mk #[0,0,128]) ||
      raw == (ByteArray.mk #[0,255]) then return false
  let branch : Sum Nat UInt8 := if n % 2 == 0 then .inl n else .inr b
  if branch.ctorIdx != n % 2 then return false
  let result := replaceBytes raw 6 [b]
  if fileRange result 0 7 != [0,255,128,0,0,0,b] || fileRange result 9 16 != [] then return false
  if (ByteArray.mk result.data).data.toList != result.data.toList then return false
  let xs := ([n,n+1,7] : List Nat).toArray.push 8
  if xs.pop.toList != [n,n+1,7] then return false
  let mut tree : Std.TreeMap Nat UInt8 := {}
  for i in List.range 16 do tree := tree.insert (n+i) (i.toUInt8)
  if tree[n+8]? != some 8 || (tree.erase (n+8))[n+8]?.isSome then return false
  let text := String.ofList ['λ',Char.ofNat 0,'🙂']
  if text.length != 3 || text.utf8ByteSize != 7 || (String.fromUTF8? text.toUTF8) != some text then return false
  let big := 0x10000000000000000+n
  if (big*127)/127 != big || (big*127)%127 != 0 || Nat.gcd (big*3) big != big then return false
  let neg := -(Int.ofNat big)
  if (neg.ediv 17)*17 + neg.emod 17 != neg then return false
  if b.toNat != n%256 || (b.toUInt32 >>> 1).toNat != n%256/2 then return false
  return true

def main (args : List String) : IO UInt32 := do
  let some n := args.head?.bind String.toNat? | return 2
  let out ← IO.getStdout
  out.putStrLn "G1_REVIEW_BEGIN"
  out.flush
  let answer := primitiveChecks n
  if answer then out.putStrLn "G1_REVIEW_PASS" else out.putStrLn "G1_REVIEW_FAIL"
  out.flush
  return if answer then 0 else 1
