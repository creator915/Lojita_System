import Lean
import Lojita.Kernel.KernelLimits
import Lojita.Kernel.SyntaxTriage

namespace Lojita.Kernel
open Lean Elab

/-- Upper bound on closed exponents `b` in `a ^ b` (`a > 1`) or `a <<< b` (`a > 0`) (T7-①). -/
def maxSafeClosedExponent : Nat := 65536

/-- Threshold for flagging structural recursion over huge closed fuel constants (T7-②). -/
def largeFuelThreshold : Nat := 4096

/-- Bounded closed small-Nat evaluator (capped at `10^12` and 64 steps so it never allocates big GMP ints). -/
def evalSmallNat? (env : Environment) (e : Expr) (fuel : Nat := 64) : Option Nat := Id.run do
  let cap := 1000000000000 -- 10^12
  let rec go (cur : Expr) (rem : Nat) : Option Nat :=
    match rem with
    | 0 => none
    | rem' + 1 =>
      let cur := cur.consumeMData
      match cur with
      | .lit (.natVal n) => some n
      | .const ``Nat.zero _ => some 0
      | .const ``UInt64.size _ => some UInt64.size
      | .const ``UInt32.size _ => some UInt32.size
      | .const ``UInt16.size _ => some UInt16.size
      | .const ``UInt8.size _ => some UInt8.size
      | .const ``USize.size _ => some UInt64.size
      | .const n _ =>
        match env.find? n with
        | some (.defnInfo d) =>
          if d.levelParams.isEmpty then go d.value rem' else none
        | _ => none
      | .app (.const ``Nat.succ _) a => do
        let va ← go a rem'
        some (va + 1)
      | _ =>
        let fn := cur.getAppFn.consumeMData
        let args := cur.getAppArgs
        if fn.isConstOf ``OfNat.ofNat && args.size >= 2 then
          go args[1]! rem'
        else if (fn.isConstOf ``Nat.add || fn.isConstOf ``HAdd.hAdd) && args.size >= 2 then do
          let va ← go args[args.size - 2]! rem'
          let vb ← go args[args.size - 1]! rem'
          let s := va + vb
          if s <= cap then some s else some (cap + 1)
        else if (fn.isConstOf ``Nat.mul || fn.isConstOf ``HMul.hMul) && args.size >= 2 then do
          let va ← go args[args.size - 2]! rem'
          let vb ← go args[args.size - 1]! rem'
          let p := va * vb
          if p <= cap then some p else some (cap + 1)
        else if (fn.isConstOf ``Nat.sub || fn.isConstOf ``HSub.hSub) && args.size >= 2 then do
          let va ← go args[args.size - 2]! rem'
          let vb ← go args[args.size - 1]! rem'
          some (va - vb)
        else if (fn.isConstOf ``Nat.pow || fn.isConstOf ``HPow.hPow) && args.size >= 2 then do
          let va ← go args[args.size - 2]! rem'
          let vb ← go args[args.size - 1]! rem'
          if va <= 1 then some va
          else if vb <= 40 then
            let p := va ^ vb
            if p <= cap then some p else some (cap + 1)
          else
            some (cap + 1)
        else
          none
  go e fuel

/-- Explicit-stack $O(|DAG|)$ pointer/hash-deduplicated `Expr` inspector for newly elaborated constants.
    - Rejects closed `a ^ b` (`a > 1`, `b > 65536`) and `a <<< b` (`a > 0`, `b > 65536`) (`TABOO_HUGE_POW_SHIFT`);
    - Detects structural recursion applied to closed numerals `> 4096` (`largeFuelDefs`). -/
def inspectExprDAG (env : Environment) (declName : Name) (roots : Array Expr) :
    Except TabooError Bool := do
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array Expr := roots
  let mut usesLargeFuel := false
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ | .const _ _ =>
      pure ()
    | .mdata _ b | .proj _ _ b =>
      stack := stack.push b
    | .lam _ t b _ | .forallE _ t b _ =>
      stack := (stack.push b).push t
    | .letE _ t v b _ =>
      stack := ((stack.push b).push v).push t
    | .app .. =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      -- T7-①: Closed giant power or left-shift
      if (fn.isConstOf ``Nat.pow && args.size == 2) ||
         (fn.isConstOf ``HPow.hPow && args.size == 6) then
        let baseExpr := args[args.size - 2]!
        let expExpr  := args[args.size - 1]!
        if let (some a, some b) := (evalSmallNat? env baseExpr, evalSmallNat? env expExpr) then
          if a > 1 && b > maxSafeClosedExponent then
            throw {
              code   := .hugePowShift
              detail := s!"in `{declName}`: closed power `{a} ^ {b}` has exponent > {maxSafeClosedExponent}"
            }
      if (fn.isConstOf ``Nat.shiftLeft && args.size == 2) ||
         (fn.isConstOf ``HShiftLeft.hShiftLeft && args.size == 6) then
        let valExpr   := args[args.size - 2]!
        let shiftExpr := args[args.size - 1]!
        if let (some a, some b) := (evalSmallNat? env valExpr, evalSmallNat? env shiftExpr) then
          if a > 0 && b > maxSafeClosedExponent then
            throw {
              code   := .hugePowShift
              detail := s!"in `{declName}`: closed shift `{a} <<< {b}` has shift > {maxSafeClosedExponent}"
            }
      -- T7-②: Large closed structural recursion fuel
      if fn.isConstOf ``Nat.brecOn && args.size >= 2 then
        if (evalSmallNat? env args[1]!).any (· > largeFuelThreshold) then
          usesLargeFuel := true
      if (fn.isConstOf ``Nat.rec || fn.isConstOf ``Nat.casesOn) && args.size >= 4 then
        if (evalSmallNat? env args[3]!).any (· > largeFuelThreshold) then
          usesLargeFuel := true
      if let .const callee _ := fn then
        if let some (.defnInfo d) := env.find? callee then
          if !args.isEmpty && (d.value.getUsedConstantsAsSet.contains ``Nat.brecOn) then
            for arg in args do
              if (evalSmallNat? env arg).any (· > largeFuelThreshold) then
                usesLargeFuel := true
      stack := stack.push fn
      for arg in args do
        stack := stack.push arg
  return usesLargeFuel

/-- Keep anonymous `example` declarations as private definitions so they receive full kernel + axiom audit. -/
private def auditCommand (cmd : Syntax) : Command.CommandElabM Syntax := do
  let d := cmd[1]
  unless cmd.isOfKind ``Parser.Command.declaration && d.isOfKind ``Parser.Command.example do
    return cmd
  let id := mkIdent (← Command.liftCoreM (mkFreshUserName `objectExample))
  let sig : TSyntax ``Parser.Command.optDeclSig := ⟨d[1]⟩
  let rhs : TSyntax ``Parser.Command.declVal := ⟨d[2]⟩
  return (← `(private def $id:ident $sig:optDeclSig $rhs:declVal)).raw

private def cmdHasTacticWord (cmd : Syntax) (word : String) : Bool :=
  (leavesIter #[cmd]).any fun l =>
    (if l.isIdent then l.getId.toString else l.getAtomVal) == word

/-- Detect `theorem` / `example` declarations proved solely by `:= rfl` or `:= by rfl`
    (including `unseal ... in theorem ... := rfl`) so runaway WHNF reduction in `rfl`
    trips fast (~150 ms) while large `def` tables keep full budget. -/
private def isRflOnlyTheorem (cmd : Syntax) : Bool := Id.run do
  let mut cur := cmd
  while cur.isOfKind ``Parser.Command.in do
    cur := cur[1]
  unless cur.isOfKind ``Parser.Command.declaration do return false
  let d := cur[1]
  unless d.isOfKind ``Parser.Command.theorem || d.isOfKind ``Parser.Command.example do return false
  let rhs := if d.isOfKind ``Parser.Command.example then d[2] else d[3]
  let toks := (leavesIter #[rhs]).map fun l =>
    if l.isIdent then l.getId.toString else l.getAtomVal
  return toks == #[":=", "rfl"] || toks == #[":=", "by", "rfl"]

private def isWFHelperConst (c : Name) : Bool :=
  c.getRoot == `WellFounded || c == ``Acc.rec

private def constUsesWF (env : Environment) (n : Name) : Bool := Id.run do
  let some (.defnInfo d) := env.find? n | return false
  let used := d.value.getUsedConstantsAsSet
  if used.any isWFHelperConst then
    return true
  for c in used do
    if let some (.defnInfo d2) := env.find? c then
      if d2.value.getUsedConstantsAsSet.any isWFHelperConst then
        return true
  return false

private def envMentionsWF (env : Environment) (currNs : Name) (cmd : Syntax) : Bool := Id.run do
  for leaf in leavesIter #[cmd] do
    if leaf.isIdent then
      if isWFHelperConst leaf.getId then
        return true
      for n in [leaf.getId, env.mainModule ++ leaf.getId, currNs ++ leaf.getId] do
        if constUsesWF env n || constUsesWF env (mkPrivateName env n) then
          return true
  return false

/-- Classify elaboration timeouts / recursion / memory faults into precise `TabooError` diagnostics. -/
private def classifyElabFailure (env : Environment) (currNs : Name) (cmd : Syntax) (msg : String) : String :=
  let offset := (cmd.getPos?.getD 0).byteIdx
  let isHeartbeat := msg.contains "deterministic timeout" || msg.contains "heartbeats"
  let isDeepRec   := msg.contains "maximum recursion depth" || msg.contains "deep recursion"
  let isMem       := msg.contains "excessive memory"
  if !isHeartbeat && !isDeepRec && !isMem then
    s!"ELABORATION_ERROR: {msg}"
  else
    let code : TabooCode :=
      if isMem then .excessiveMemory
      else if cmdHasTacticWord cmd "decide" then .decideTimeout
      else if cmdHasTacticWord cmd "rfl" && envMentionsWF env currNs cmd then .wfKernelUnfold
      else if isDeepRec then .deepRecursion
      else if cmdHasTacticWord cmd "rfl" then .rflReductionBlowup
      else .kernelTimeout
    toString ({ code, offset, detail := msg : TabooError })

structure ElabGuardedResult where
  env           : Environment
  steps         : Array Environment
  largeFuelDefs : NameSet

/-- Stage 2: Elaborate commands sequentially on a dedicated 64 MiB worker thread with per-command
    `withCurrHeartbeats`, `safeElabOptions` (`postponeCompile := true`, `maxRecDepth := 2048`),
    and post-command `Expr` DAG inspection (`TABOO_HUGE_POW_SHIFT` & `largeFuelDefs`). -/
def elabCommandsGuarded (env : Environment) (src : String) (cmds : Array Syntax)
    (stagedData := false) (opts : Options := safeElabOptions) : IO ElabGuardedResult := do
  initKernelLimits
  let task ← IO.asTask (prio := .dedicated) do
    let ctx : Command.Context := {
      fileName := env.mainModule.toString
      fileMap  := src.toFileMap
      snap?    := none
      cancelTk? := none
    }
    let state := Command.mkState env {} opts
    let state := {
      state with
      infoState := { enabled := false }
      scopes    := state.scopes.map fun s => { s with isNoncomputable := stagedData }
    }
    let action : Command.CommandElabM (Except String (Array Environment × NameSet)) := do
      let mut steps := #[]
      let mut largeFuel : NameSet := {}
      let mut prevConsts : NameSet :=
        (← getEnv).checked.get.constants.foldStage2 (fun acc n _ => acc.insert n) {}
      for cmd in cmds do
        let curEnvBefore ← getEnv
        let curNsBefore ← getCurrNamespace
        let savedScopes := (← get).scopes
        if isRflOnlyTheorem cmd then
          modify fun s => {
            s with scopes := s.scopes.map fun sc =>
              { sc with opts := sc.opts.set `maxHeartbeats (2000 : Nat) }
          }
        try
          let cmd' ← auditCommand cmd
          -- `elabCommandTopLevel` creates a fresh per-command `Core.Context` with `initHeartbeats`.
          Command.elabCommandTopLevel cmd'
          if isRflOnlyTheorem cmd then
            modify fun s => { s with scopes := savedScopes }
        catch ex =>
          modify fun s => { s with scopes := savedScopes }
          let emsg ← ex.toMessageData.toString
          return .error (classifyElabFailure curEnvBefore curNsBefore cmd emsg)
        let log := (← get).messages
        if log.hasErrors then
          let messages ← log.toList.mapM fun m => m.toString
          let joined := String.intercalate "\n" messages
          return .error (classifyElabFailure curEnvBefore curNsBefore cmd joined)
        if log.toList.any (·.kind == `hasSorry) then
          return .error "SORRY_AXIOM_VIOLATION: elaborated declaration uses sorryAx"
        let curEnv ← getEnv
        let kenv := curEnv.checked.get
        let newNames := kenv.constants.foldStage2 (fun acc n _ =>
          if prevConsts.contains n then acc else acc.push n) #[]
        for n in newNames do
          prevConsts := prevConsts.insert n
          if let some info := kenv.find? n then
            let roots := match info.value? (allowOpaque := true) with
              | some v => #[info.type, v]
              | none   => #[info.type]
            match inspectExprDAG curEnv n roots with
            | .error te =>
              let te := { te with offset := (cmd.getPos?.getD 0).byteIdx }
              return .error (toString te)
            | .ok hasLargeFuel =>
              if hasLargeFuel then largeFuel := largeFuel.insert n
        steps := steps.push curEnv
      return .ok (steps, largeFuel)
    match ← EIO.toIO' ((action ctx).run state) with
    | .error e =>
      throw (IO.userError s!"ELABORATION_ERROR: {← e.toMessageData.toString}")
    | .ok (.error formatted, _) =>
      throw (IO.userError formatted)
    | .ok (.ok (steps, largeFuel), st) =>
      return { env := st.env, steps, largeFuelDefs := largeFuel }
  IO.ofExcept (← IO.wait task)

end Lojita.Kernel
