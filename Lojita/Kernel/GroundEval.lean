import Lean
import Lojita.Kernel.AxiomGuard

namespace Lojita.Kernel
open Lean

/-- Ground runtime type tags ensuring fast refutation only compares values of identical Lean types. -/
inductive GroundTy where
  | nat | int | bool | ordering | char
  | uint8 | uint16 | uint32 | uint64
  | bitvec (w : Nat)
  | str | byteArray
  | prod (a b : GroundTy)
  | option (a : GroundTy)
  | sum (a b : GroundTy)
  | list (a : GroundTy)
  | array (a : GroundTy)
  deriving BEq, Repr, Inhabited

/-- Canonical ground values evaluated purely on the heap without invoking kernel WHNF. -/
inductive GroundVal where
  | nat (v : Nat)
  | int (v : Int)
  | bool (v : Bool)
  | ordering (v : Ordering)
  | char (v : Char)
  | uint8 (v : UInt8)
  | uint16 (v : UInt16)
  | uint32 (v : UInt32)
  | uint64 (v : UInt64)
  | bitvec (w : Nat) (v : Nat)
  | str (utf8 : ByteArray)
  | byteArray (bs : ByteArray)
  | prod (fst snd : GroundVal)
  | option (ty : GroundTy) (val : Option GroundVal)
  | sum (lty rty : GroundTy) (isRight : Bool) (val : GroundVal)
  | list (elemTy : GroundTy) (items : Array GroundVal)
  | array (elemTy : GroundTy) (items : Array GroundVal)
  deriving BEq, Inhabited

def GroundVal.ty : GroundVal → GroundTy
  | .nat _             => .nat
  | .int _             => .int
  | .bool _            => .bool
  | .ordering _        => .ordering
  | .char _            => .char
  | .uint8 _           => .uint8
  | .uint16 _          => .uint16
  | .uint32 _          => .uint32
  | .uint64 _          => .uint64
  | .bitvec w _        => .bitvec w
  | .str _             => .str
  | .byteArray _       => .byteArray
  | .prod a b          => .prod a.ty b.ty
  | .option t _        => .option t
  | .sum lt rt _ _     => .sum lt rt
  | .list t _          => .list t
  | .array t _         => .array t

def GroundVal.containerSize : GroundVal → Nat
  | .str utf8      => utf8.size
  | .byteArray bs  => bs.size
  | .list _ items  => items.size
  | .array _ items => items.size
  | _              => 1

/-- Decode a `Expr` representing a closed ground type into `GroundTy`. -/
partial def decodeGroundTy? (env : Environment) (e : Expr) : Option GroundTy :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let .const c _ := fn then
    if c == ``Nat && args.isEmpty then some .nat
    else if c == ``Int && args.isEmpty then some .int
    else if c == ``Bool && args.isEmpty then some .bool
    else if c == ``Ordering && args.isEmpty then some .ordering
    else if c == ``Char && args.isEmpty then some .char
    else if c == ``UInt8 && args.isEmpty then some .uint8
    else if c == ``UInt16 && args.isEmpty then some .uint16
    else if c == ``UInt32 && args.isEmpty then some .uint32
    else if c == ``UInt64 && args.isEmpty then some .uint64
    else if c == ``String && args.isEmpty then some .str
    else if c == ``ByteArray && args.isEmpty then some .byteArray
    else if c == `LojitaCtx.Terminal.Byte && args.isEmpty then some .uint8
    else if c == `LojitaCtx.Terminal.Bytes && args.isEmpty then some (.list .uint8)
    else if c == ``BitVec && args.size == 1 then
      match args[0]!.consumeMData with
      | .lit (.natVal w) => some (.bitvec w)
      | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal w))) _ => some (.bitvec w)
      | _ => none
    else if c == ``Prod && args.size == 2 then do
      return .prod (← decodeGroundTy? env args[0]!) (← decodeGroundTy? env args[1]!)
    else if c == ``Option && args.size == 1 then do
      return .option (← decodeGroundTy? env args[0]!)
    else if c == ``Sum && args.size == 2 then do
      return .sum (← decodeGroundTy? env args[0]!) (← decodeGroundTy? env args[1]!)
    else if c == ``List && args.size == 1 then do
      return .list (← decodeGroundTy? env args[0]!)
    else if c == ``Array && args.size == 1 then do
      return .array (← decodeGroundTy? env args[0]!)
    else
      match env.find? c with
      | some (.defnInfo d) =>
        if d.hints matches .abbrev && d.levelParams.isEmpty && args.isEmpty then
          decodeGroundTy? env d.value
        else none
      | _ => none
  else
    none

/-- Verify that a typeclass instance expression is closed and built purely from `Init` constants. -/
private def isPureInitInstance (env : Environment) (inst : Expr) : Bool :=
  let inst := inst.consumeMData
  if inst.isAppOfArity ``instOfNatNat 1 then true
  else
    !inst.hasLooseBVars && !inst.hasFVar && !inst.hasMVar &&
      inst.getUsedConstantsAsSet.all fun c => (moduleOf? env c).any (·.getRoot == `Init)

private inductive OpKind where
  | natSucc | natAdd | natSub | natMul
  | intOfNat | intNegSucc | intNeg
  | charOfNat | charMk
  | uint8OfNat | uint16OfNat | uint32OfNat | uint64OfNat
  | bitvecOfNat (w : Nat)
  | prodMk
  | optSome (ty : GroundTy)
  | sumInl (lty rty : GroundTy)
  | sumInr (lty rty : GroundTy)
  | assembleList (elemTy : GroundTy) (count : Nat)
  | listAppend (elemTy : GroundTy)
  | listToArray (elemTy : GroundTy)
  | arrayToList (elemTy : GroundTy)
  | arrayPush (elemTy : GroundTy)
  | arrayAppend (elemTy : GroundTy)
  | strSingleton | strPush | strAppend | strOfList | strToList
  | strOfByteArray | strToByteArray | strJoin | strIntercalate
  | terminalBytes
  | byteArrayMk | listToByteArray | byteArrayData | byteArrayToList
  | byteArrayPush | byteArrayAppend
  deriving Inhabited

private inductive EvalFrame where
  | eval (e : Expr)
  | apply (op : OpKind)
  | bindLocal
  | popLocal
  deriving Inhabited

private def bytesOfUInt8Vals (items : Array GroundVal) : Option ByteArray := Id.run do
  let mut ba := ByteArray.emptyWithCapacity items.size
  for item in items do
    let .uint8 b := item | return none
    ba := ba.push b
  return some ba

private def charsOfVals (items : Array GroundVal) : Option (List Char) := Id.run do
  let mut out : Array Char := Array.mkEmpty items.size
  for item in items do
    let .char c := item | return none
    out := out.push c
  return some out.toList

private def stringFromUtf8Checked? (ba : ByteArray) : Option String :=
  String.fromUTF8? ba

/-- Explicit-stack bounded closed ground expression evaluator (`budget := 131072` steps).
    Zero C++ call-stack recursion: unrolls `List.cons` spines iteratively in $O(1)$ frames. -/
def evalGround? (env : Environment) (root : Expr) (budget : Nat := 131072) : Option GroundVal := Id.run do
  if root.hasLooseBVars || root.hasFVar || root.hasMVar then return none
  let mut work : Array EvalFrame := #[.eval root]
  let mut vals : Array GroundVal := #[]
  let mut locals : Array GroundVal := #[]
  let mut instCache : Std.HashMap Expr Bool := {}
  let mut tyCache : Std.HashMap Expr (Option GroundTy) := {}
  let mut steps := 0
  while !work.isEmpty do
    steps := steps + 1
    if steps > budget then return none
    let frame := work.back!
    work := work.pop
    match frame with
    | .bindLocal =>
      let some v := vals.back? | return none
      vals := vals.pop
      locals := locals.push v
    | .popLocal =>
      if locals.isEmpty then return none
      locals := locals.pop
    | .eval raw =>
      let e := raw.consumeMData
      match e with
      | .bvar idx =>
        if idx >= locals.size then return none
        vals := vals.push locals[locals.size - 1 - idx]!
      | .letE _ _ val body _ =>
        -- Lean's `%[a, b, ... | nil]` desugaring for lists/arrays ≥ 32 elements builds binary `let` trees!
        work := (((work.push .popLocal).push (.eval body)).push .bindLocal).push (.eval val)
      | .lit (.natVal n) => vals := vals.push (.nat n)
      | .lit (.strVal s) => vals := vals.push (.str s.toByteArray)
      | .proj ``String 0 s =>
        work := (work.push (.apply .strToByteArray)).push (.eval s)
      | .proj ``ByteArray 0 ba =>
        work := (work.push (.apply .byteArrayData)).push (.eval ba)
      | .proj ``Array 0 _ =>
        return none
      | _ =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        if let .lam _ _ body _ := fn then
          -- `PreDefinition.letToHave` turns `let left := val; body` into `have` = `(fun left => body) val`!
          if args.size == 1 then
            work := (((work.push .popLocal).push (.eval body)).push .bindLocal).push (.eval args[0]!)
          else
            return none
        else
        let .const c _ := fn | return none
        -- Nullary constructors & constants
        if c == ``Nat.zero && args.isEmpty then
          vals := vals.push (.nat 0)
        else if c == ``Bool.true && args.isEmpty then
          vals := vals.push (.bool true)
        else if c == ``Bool.false && args.isEmpty then
          vals := vals.push (.bool false)
        else if c == ``Ordering.lt && args.isEmpty then
          vals := vals.push (.ordering .lt)
        else if c == ``Ordering.eq && args.isEmpty then
          vals := vals.push (.ordering .eq)
        else if c == ``Ordering.gt && args.isEmpty then
          vals := vals.push (.ordering .gt)
        else if c == ``ByteArray.empty && args.isEmpty then
          vals := vals.push (.byteArray ByteArray.empty)
        else if c == ``ByteArray.emptyWithCapacity && args.size == 1 then
          vals := vals.push (.byteArray ByteArray.empty)
        -- Numeric literals via `OfNat.ofNat α (.lit (.natVal n)) inst`
        else if c == ``OfNat.ofNat && args.size == 3 then
          let tyExpr := args[0]!
          let gty? := match tyCache[tyExpr]? with
            | some cached => cached
            | none => decodeGroundTy? env tyExpr
          tyCache := tyCache.insert tyExpr gty?
          let some gty := gty? | return none
          let .lit (.natVal n) := args[1]!.consumeMData | return none
          let instExpr := args[2]!
          let okInst := match instCache[instExpr]? with
            | some ok => ok
            | none    => isPureInitInstance env instExpr
          instCache := instCache.insert instExpr okInst
          unless okInst do return none
          match gty with
          | .nat       => vals := vals.push (.nat n)
          | .int       => vals := vals.push (.int (Int.ofNat n))
          | .uint8     => vals := vals.push (.uint8 (UInt8.ofNat n))
          | .uint16    => vals := vals.push (.uint16 (UInt16.ofNat n))
          | .uint32    => vals := vals.push (.uint32 (UInt32.ofNat n))
          | .uint64    => vals := vals.push (.uint64 (UInt64.ofNat n))
          | .bitvec w  =>
            if w <= 256 then vals := vals.push (.bitvec w (n % (2 ^ w)))
            else return none
          | _ => return none
        -- Nat / Int / Char / UInt / BitVec constructors
        else if c == ``Nat.succ && args.size == 1 then
          work := (work.push (.apply .natSucc)).push (.eval args[0]!)
        else if c == ``Nat.add && args.size == 2 then
          work := ((work.push (.apply .natAdd)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``HAdd.hAdd && args.size == 6 && args[0]!.consumeMData.isConstOf ``Nat &&
                args[1]!.consumeMData.isConstOf ``Nat && isPureInitInstance env args[3]! then
          work := ((work.push (.apply .natAdd)).push (.eval args[5]!)).push (.eval args[4]!)
        else if c == ``Nat.sub && args.size == 2 then
          work := ((work.push (.apply .natSub)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``HSub.hSub && args.size == 6 && args[0]!.consumeMData.isConstOf ``Nat &&
                args[1]!.consumeMData.isConstOf ``Nat && isPureInitInstance env args[3]! then
          work := ((work.push (.apply .natSub)).push (.eval args[5]!)).push (.eval args[4]!)
        else if c == ``Nat.mul && args.size == 2 then
          work := ((work.push (.apply .natMul)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``HMul.hMul && args.size == 6 && args[0]!.consumeMData.isConstOf ``Nat &&
                args[1]!.consumeMData.isConstOf ``Nat && isPureInitInstance env args[3]! then
          work := ((work.push (.apply .natMul)).push (.eval args[5]!)).push (.eval args[4]!)
        else if c == ``Int.ofNat && args.size == 1 then
          work := (work.push (.apply .intOfNat)).push (.eval args[0]!)
        else if c == ``Int.negSucc && args.size == 1 then
          work := (work.push (.apply .intNegSucc)).push (.eval args[0]!)
        else if c == ``Neg.neg && args.size == 3 && args[0]!.consumeMData.isConstOf ``Int &&
                isPureInitInstance env args[1]! then
          work := (work.push (.apply .intNeg)).push (.eval args[2]!)
        else if c == ``Char.ofNat && args.size == 1 then
          work := (work.push (.apply .charOfNat)).push (.eval args[0]!)
        else if c == ``Char.mk && args.size == 2 then
          work := (work.push (.apply .charMk)).push (.eval args[0]!)
        else if (c == ``UInt8.ofNat || c == `LojitaCtx.Terminal.byte) && args.size == 1 then
          work := (work.push (.apply .uint8OfNat)).push (.eval args[0]!)
        else if c == ``UInt8.ofBitVec && args.size == 1 then
          -- `UInt8.ofBitVec (BitVec.ofFin (Fin.mk n _))`
          let bv := args[0]!.consumeMData
          if bv.isAppOfArity ``BitVec.ofFin 2 then
            let fin := (bv.getArg! 1).consumeMData
            if fin.isAppOfArity ``Fin.mk 3 then
              work := (work.push (.apply .uint8OfNat)).push (.eval (fin.getArg! 1))
            else return none
          else return none
        else if c == ``UInt16.ofNat && args.size == 1 then
          work := (work.push (.apply .uint16OfNat)).push (.eval args[0]!)
        else if c == ``UInt32.ofNat && args.size == 1 then
          work := (work.push (.apply .uint32OfNat)).push (.eval args[0]!)
        else if c == ``UInt64.ofNat && args.size == 1 then
          work := (work.push (.apply .uint64OfNat)).push (.eval args[0]!)
        else if c == ``BitVec.ofNat && args.size == 2 then
          let .lit (.natVal w) := args[0]!.consumeMData | return none
          if w > 256 then return none
          work := (work.push (.apply (.bitvecOfNat w))).push (.eval args[1]!)
        else if c == ``BitVec.ofFin && args.size == 2 then
          let .lit (.natVal w) := args[0]!.consumeMData | return none
          if w > 256 then return none
          let fin := args[1]!.consumeMData
          if fin.isAppOfArity ``Fin.mk 3 then
            work := (work.push (.apply (.bitvecOfNat w))).push (.eval (fin.getArg! 1))
          else return none
        -- Algebraic composites: Prod, Option, Sum
        else if c == ``Prod.mk && args.size == 4 then
          work := ((work.push (.apply .prodMk)).push (.eval args[3]!)).push (.eval args[2]!)
        else if c == ``Option.none && args.size == 1 then
          let some ty := decodeGroundTy? env args[0]! | return none
          vals := vals.push (.option ty none)
        else if c == ``Option.some && args.size == 2 then
          let some ty := decodeGroundTy? env args[0]! | return none
          work := (work.push (.apply (.optSome ty))).push (.eval args[1]!)
        else if c == ``Sum.inl && args.size == 3 then
          let some lty := decodeGroundTy? env args[0]! | return none
          let some rty := decodeGroundTy? env args[1]! | return none
          work := (work.push (.apply (.sumInl lty rty))).push (.eval args[2]!)
        else if c == ``Sum.inr && args.size == 3 then
          let some lty := decodeGroundTy? env args[0]! | return none
          let some rty := decodeGroundTy? env args[1]! | return none
          work := (work.push (.apply (.sumInr lty rty))).push (.eval args[2]!)
        -- Lists (unroll `List.cons` spine iteratively to keep stack small!)
        else if c == ``List.nil && args.size == 1 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          vals := vals.push (.list elemTy #[])
        else if c == ``List.cons && args.size == 3 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          let mut heads : Array Expr := #[args[1]!]
          let mut curTail := args[2]!.consumeMData
          while curTail.isAppOfArity ``List.cons 3 do
            steps := steps + 1
            if steps > budget then return none
            heads := heads.push (curTail.getArg! 1)
            curTail := (curTail.getArg! 2).consumeMData
          if curTail.isAppOfArity ``List.nil 1 then
            work := work.push (.apply (.assembleList elemTy heads.size))
            let mut k := heads.size
            while k > 0 do
              k := k - 1
              work := work.push (.eval heads[k]!)
          else
            -- Non-nil tail (e.g. `x :: ys`): evaluate heads ++ tail via listAppend
            work := work.push (.apply (.listAppend elemTy))
            work := work.push (.eval curTail)
            work := work.push (.apply (.assembleList elemTy heads.size))
            let mut k := heads.size
            while k > 0 do
              k := k - 1
              work := work.push (.eval heads[k]!)
        else if c == ``List.append && args.size == 3 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          work := ((work.push (.apply (.listAppend elemTy))).push (.eval args[2]!)).push (.eval args[1]!)
        -- Arrays
        else if (c == ``List.toArray || c == ``Array.mk) && args.size == 2 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          work := (work.push (.apply (.listToArray elemTy))).push (.eval args[1]!)
        else if c == ``Array.toList && args.size == 2 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          work := (work.push (.apply (.arrayToList elemTy))).push (.eval args[1]!)
        else if c == ``Array.empty && args.size == 1 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          vals := vals.push (.array elemTy #[])
        else if (c == ``Array.emptyWithCapacity || c == ``Array.mkEmpty) && args.size == 2 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          vals := vals.push (.array elemTy #[])
        else if c == ``Array.push && args.size == 3 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          work := ((work.push (.apply (.arrayPush elemTy))).push (.eval args[2]!)).push (.eval args[1]!)
        else if c == ``Array.append && args.size == 3 then
          let some elemTy := decodeGroundTy? env args[0]! | return none
          work := ((work.push (.apply (.arrayAppend elemTy))).push (.eval args[2]!)).push (.eval args[1]!)
        -- Strings & UTF-8 / ByteArray
        else if c == ``String.singleton && args.size == 1 then
          work := (work.push (.apply .strSingleton)).push (.eval args[0]!)
        else if c == ``String.push && args.size == 2 then
          work := ((work.push (.apply .strPush)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``String.append && args.size == 2 then
          work := ((work.push (.apply .strAppend)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``String.ofList && args.size == 1 then
          work := (work.push (.apply .strOfList)).push (.eval args[0]!)
        else if c == ``String.toList && args.size == 1 then
          work := (work.push (.apply .strToList)).push (.eval args[0]!)
        else if c == ``String.ofByteArray && args.size == 2 then
          -- Second argument is `isValidUTF8 : Prop` proof (already checked in original module)
          work := (work.push (.apply .strOfByteArray)).push (.eval args[0]!)
        else if (c == ``String.toByteArray || c == ``String.toUTF8) && args.size == 1 then
          work := (work.push (.apply .strToByteArray)).push (.eval args[0]!)
        else if c == ``String.join && args.size == 1 then
          work := (work.push (.apply .strJoin)).push (.eval args[0]!)
        else if c == ``String.intercalate && args.size == 2 then
          work := ((work.push (.apply .strIntercalate)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == `LojitaCtx.Terminal.bytes && args.size == 1 then
          work := (work.push (.apply .terminalBytes)).push (.eval args[0]!)
        else if c == ``ByteArray.mk && args.size == 1 then
          work := (work.push (.apply .byteArrayMk)).push (.eval args[0]!)
        else if c == ``List.toByteArray && args.size == 1 then
          work := (work.push (.apply .listToByteArray)).push (.eval args[0]!)
        else if c == ``ByteArray.data && args.size == 1 then
          work := (work.push (.apply .byteArrayData)).push (.eval args[0]!)
        else if c == ``ByteArray.toList && args.size == 1 then
          work := (work.push (.apply .byteArrayToList)).push (.eval args[0]!)
        else if c == ``ByteArray.push && args.size == 2 then
          work := ((work.push (.apply .byteArrayPush)).push (.eval args[1]!)).push (.eval args[0]!)
        else if c == ``ByteArray.append && args.size == 2 then
          work := ((work.push (.apply .byteArrayAppend)).push (.eval args[1]!)).push (.eval args[0]!)
        -- Polymorphic `HAppend.hAppend α α α inst a b` with verified `Init` instance
        else if c == ``HAppend.hAppend && args.size == 6 &&
                args[0]! == args[1]! && args[1]! == args[2]! &&
                isPureInitInstance env args[3]! then
          let some gty := decodeGroundTy? env args[0]! | return none
          match gty with
          | .str =>
            work := ((work.push (.apply .strAppend)).push (.eval args[5]!)).push (.eval args[4]!)
          | .byteArray =>
            work := ((work.push (.apply .byteArrayAppend)).push (.eval args[5]!)).push (.eval args[4]!)
          | .list elemTy =>
            work := ((work.push (.apply (.listAppend elemTy))).push (.eval args[5]!)).push (.eval args[4]!)
          | .array elemTy =>
            work := ((work.push (.apply (.arrayAppend elemTy))).push (.eval args[5]!)).push (.eval args[4]!)
          | _ => return none
        else
          return none
    | .apply op =>
      match op with
      | .natSucc =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.nat (a + 1))
      | .natAdd =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.nat va, .nat vb) := (a, b) | return none
        vals := vals.push (.nat (va + vb))
      | .natSub =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.nat va, .nat vb) := (a, b) | return none
        vals := vals.push (.nat (va - vb))
      | .natMul =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.nat va, .nat vb) := (a, b) | return none
        vals := vals.push (.nat (va * vb))
      | .intOfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.int (Int.ofNat a))
      | .intNegSucc =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.int (Int.negSucc a))
      | .intNeg =>
        let some (.int a) := vals.back? | return none
        vals := vals.pop.push (.int (-a))
      | .charOfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.char (Char.ofNat a))
      | .charMk =>
        let some (.uint32 u) := vals.back? | return none
        vals := vals.pop.push (.char (Char.ofNat u.toNat))
      | .uint8OfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.uint8 (UInt8.ofNat a))
      | .uint16OfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.uint16 (UInt16.ofNat a))
      | .uint32OfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.uint32 (UInt32.ofNat a))
      | .uint64OfNat =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.uint64 (UInt64.ofNat a))
      | .bitvecOfNat w =>
        let some (.nat a) := vals.back? | return none
        vals := vals.pop.push (.bitvec w (a % (2 ^ w)))
      | .prodMk =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        vals := vals.push (.prod a b)
      | .optSome ty =>
        let some v := vals.back? | return none
        if v.ty != ty then return none
        vals := vals.pop.push (.option ty (some v))
      | .sumInl lty rty =>
        let some v := vals.back? | return none
        if v.ty != lty then return none
        vals := vals.pop.push (.sum lty rty false v)
      | .sumInr lty rty =>
        let some v := vals.back? | return none
        if v.ty != rty then return none
        vals := vals.pop.push (.sum lty rty true v)
      | .assembleList elemTy count =>
        if vals.size < count then return none
        let start := vals.size - count
        let slice := vals.extract start vals.size
        if slice.any (·.ty != elemTy) then return none
        vals := (vals.shrink start).push (.list elemTy slice)
      | .listAppend elemTy =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.list t1 xs, .list t2 ys) := (a, b) | return none
        if t1 != elemTy || t2 != elemTy then return none
        vals := vals.push (.list elemTy (xs ++ ys))
      | .listToArray elemTy =>
        let some (.list t xs) := vals.back? | return none
        if t != elemTy then return none
        vals := vals.pop.push (.array elemTy xs)
      | .arrayToList elemTy =>
        let some (.array t xs) := vals.back? | return none
        if t != elemTy then return none
        vals := vals.pop.push (.list elemTy xs)
      | .arrayPush elemTy =>
        if vals.size < 2 then return none
        let x := vals.back!; vals := vals.pop
        let arr := vals.back!; vals := vals.pop
        let .array t xs := arr | return none
        if t != elemTy || x.ty != elemTy then return none
        vals := vals.push (.array elemTy (xs.push x))
      | .arrayAppend elemTy =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.array t1 xs, .array t2 ys) := (a, b) | return none
        if t1 != elemTy || t2 != elemTy then return none
        vals := vals.push (.array elemTy (xs ++ ys))
      | .strSingleton =>
        let some (.char c) := vals.back? | return none
        vals := vals.pop.push (.str (String.singleton c).toByteArray)
      | .strPush =>
        if vals.size < 2 then return none
        let ch := vals.back!; vals := vals.pop
        let st := vals.back!; vals := vals.pop
        let (.str ba, .char c) := (st, ch) | return none
        vals := vals.push (.str (ba ++ (String.singleton c).toByteArray))
      | .strAppend =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.str ba1, .str ba2) := (a, b) | return none
        vals := vals.push (.str (ba1 ++ ba2))
      | .strOfList =>
        let some (.list .char items) := vals.back? | return none
        let some cs := charsOfVals items | return none
        vals := vals.pop.push (.str (String.ofList cs).toByteArray)
      | .strToList =>
        let some (.str ba) := vals.back? | return none
        let some s := stringFromUtf8Checked? ba | return none
        vals := vals.pop.push (.list .char (s.toList.toArray.map .char))
      | .strOfByteArray =>
        let some (.byteArray ba) := vals.back? | return none
        vals := vals.pop.push (.str ba)
      | .strToByteArray =>
        let some (.str ba) := vals.back? | return none
        vals := vals.pop.push (.byteArray ba)
      | .strJoin =>
        let some (.list .str items) := vals.back? | return none
        let mut acc := ByteArray.empty
        for item in items do
          let .str part := item | return none
          acc := acc ++ part
        vals := vals.pop.push (.str acc)
      | .strIntercalate =>
        if vals.size < 2 then return none
        let lst := vals.back!; vals := vals.pop
        let sep := vals.back!; vals := vals.pop
        let (.str sepBa, .list .str items) := (sep, lst) | return none
        let mut acc := ByteArray.empty
        for h : i in [:items.size] do
          if i > 0 then acc := acc ++ sepBa
          let .str part := items[i] | return none
          acc := acc ++ part
        vals := vals.push (.str acc)
      | .terminalBytes =>
        let some (.str ba) := vals.back? | return none
        vals := vals.pop.push (.list .uint8 (ba.data.map .uint8))
      | .byteArrayMk =>
        let some (.array .uint8 items) := vals.back? | return none
        let some ba := bytesOfUInt8Vals items | return none
        vals := vals.pop.push (.byteArray ba)
      | .listToByteArray =>
        let some (.list .uint8 items) := vals.back? | return none
        let some ba := bytesOfUInt8Vals items | return none
        vals := vals.pop.push (.byteArray ba)
      | .byteArrayData =>
        let some (.byteArray ba) := vals.back? | return none
        vals := vals.pop.push (.array .uint8 (ba.data.map .uint8))
      | .byteArrayToList =>
        let some (.byteArray ba) := vals.back? | return none
        vals := vals.pop.push (.list .uint8 (ba.data.toList.toArray.map .uint8))
      | .byteArrayPush =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.byteArray ba, .uint8 u) := (a, b) | return none
        vals := vals.push (.byteArray (ba.push u))
      | .byteArrayAppend =>
        if vals.size < 2 then return none
        let b := vals.back!; vals := vals.pop
        let a := vals.back!; vals := vals.pop
        let (.byteArray ba1, .byteArray ba2) := (a, b) | return none
        vals := vals.push (.byteArray (ba1 ++ ba2))
  if vals.size == 1 then some vals[0]! else none

/-! ### Pinpoint Diagnostic Formatting for Distinct Ground Values -/

private def fmtCodepoint (c : Char) : String :=
  let hex := String.ofList (Nat.toDigits 16 c.toNat |>.map Char.toUpper)
  let pad := if hex.length < 4 then String.ofList (List.replicate (4 - hex.length) '0') else ""
  "U+" ++ pad ++ hex

private def fmtByteHex (b : UInt8) : String :=
  let hex := String.ofList (Nat.toDigits 16 b.toNat |>.map Char.toUpper)
  if hex.length < 2 then "0x0" ++ hex else "0x" ++ hex

partial def GroundVal.prettyShort : GroundVal → String
  | .nat v          => toString v
  | .int v          => toString v
  | .bool v         => toString v
  | .ordering .lt   => "Ordering.lt"
  | .ordering .eq   => "Ordering.eq"
  | .ordering .gt   => "Ordering.gt"
  | .char c         => s!"'{c}' ({fmtCodepoint c})"
  | .uint8 b        => fmtByteHex b
  | .uint16 v       => toString v
  | .uint32 v       => toString v
  | .uint64 v       => toString v
  | .bitvec w v     => s!"{v}#{w}"
  | .str utf8       =>
    match stringFromUtf8Checked? utf8 with
    | some s => reprStr (if s.length > 48 then (s.take 48).toString ++ "..." else s)
    | none   => s!"<utf8:{utf8.size}B>"
  | .byteArray bs   => s!"<ByteArray:{bs.size}B>"
  | .prod a b       => s!"({a.prettyShort}, {b.prettyShort})"
  | .option _ none     => "none"
  | .option _ (some v) => s!"(some {v.prettyShort})"
  | .sum _ _ false v   => s!"(inl {v.prettyShort})"
  | .sum _ _ true v    => s!"(inr {v.prettyShort})"
  | .list _ xs      => s!"<List:{xs.size}>"
  | .array _ xs     => s!"<Array:{xs.size}>"

private def formatTextDiff (x y : Array Char) : String := Id.run do
  let n := min x.size y.size
  let mut idx := n
  for i in [:n] do
    if x[i]! != y[i]! then
      idx := i
      break
  let atPos (cs : Array Char) := (cs[idx]?.map fmtCodepoint).getD "end of text"
  return s!"\ntext differs at index {idx}: expected {atPos x}, received {atPos y} (lengths {x.size} and {y.size})"

private def formatBytesDiff (x y : ByteArray) : String := Id.run do
  let n := min x.size y.size
  let mut idx := n
  for i in [:n] do
    if x[i]! != y[i]! then
      idx := i
      break
  let atPos (bs : ByteArray) := (bs[idx]?.map fmtByteHex).getD "end of bytes"
  return s!"\nbytes differ at offset {idx}: expected {atPos x}, received {atPos y} (lengths {x.size} and {y.size})"

private def formatSeqDiff (x y : Array GroundVal) : String := Id.run do
  let n := min x.size y.size
  let mut idx := n
  for i in [:n] do
    if x[i]! != y[i]! then
      idx := i
      break
  let atPos (arr : Array GroundVal) := (arr[idx]?.map GroundVal.prettyShort).getD "end of sequence"
  return s!"\nelements differ at index {idx}: expected {atPos x}, received {atPos y} (lengths {x.size} and {y.size})"

/-- Format a pinpoint human/LLM-readable diff between two distinct ground values of identical type. -/
def formatGroundDiff (expected actual : GroundVal) : String :=
  match expected, actual with
  | .str b1, .str b2 =>
    match stringFromUtf8Checked? b1, stringFromUtf8Checked? b2 with
    | some s1, some s2 => formatTextDiff s1.toList.toArray s2.toList.toArray
    | _, _             => formatBytesDiff b1 b2
  | .list .char xs, .list .char ys
  | .array .char xs, .array .char ys =>
    match charsOfVals xs, charsOfVals ys with
    | some c1, some c2 => formatTextDiff c1.toArray c2.toArray
    | _, _             => formatSeqDiff xs ys
  | .byteArray b1, .byteArray b2 =>
    formatBytesDiff b1 b2
  | .list .uint8 xs, .list .uint8 ys
  | .array .uint8 xs, .array .uint8 ys =>
    match bytesOfUInt8Vals xs, bytesOfUInt8Vals ys with
    | some b1, some b2 => formatBytesDiff b1 b2
    | _, _             => formatSeqDiff xs ys
  | .list _ xs, .list _ ys
  | .array _ xs, .array _ ys =>
    formatSeqDiff xs ys
  | _, _ =>
    s!"\nground values differ: expected {expected.prettyShort}, received {actual.prettyShort}"

inductive GroundCheckOutcome where
  | refuted (diff : String)
  | sameGround (containerSize : Nat)
  | unknown

/-- Sound fast-refutation oracle:
    - Never accepts (`sameGround` still proceeds to `KernelGuard.checkValuesDefEq`!);
    - Immediately refutes (`refuted diff`) when both expressions evaluate to ground values
      of the exact same `GroundTy` and `g₁ != g₂`. -/
def compareGroundFast (env : Environment) (expected actual : Expr) : GroundCheckOutcome :=
  match evalGround? env expected, evalGround? env actual with
  | some g₁, some g₂ =>
    if g₁.ty == g₂.ty then
      if g₁ != g₂ then .refuted (formatGroundDiff g₁ g₂)
      else .sameGround (max g₁.containerSize g₂.containerSize)
    else .unknown
  | _, _ => .unknown

end Lojita.Kernel
