set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.Outcome`: Three-Valued Partial Evaluator Algebra, `Code` AST & Canonical S-Expr Codec
-/

namespace Prism

inductive PrismOutcome (α : Type) : Type where
  | syntaxErr  : String → PrismOutcome α
  | bot        : String → PrismOutcome α
  | translated : α → PrismOutcome α
  deriving Repr

instance {α : Type} : Inhabited (PrismOutcome α) := ⟨.bot "default"⟩

namespace PrismOutcome

def bind {α β : Type} (m : PrismOutcome α) (f : α → PrismOutcome β) : PrismOutcome β :=
  match m with
  | .syntaxErr e  => .syntaxErr e
  | .bot r        => .bot r
  | .translated a => f a

def map {α β : Type} (f : α → β) (m : PrismOutcome α) : PrismOutcome β :=
  bind m (fun a => .translated (f a))

instance : Monad PrismOutcome where
  pure := .translated
  bind := bind

end PrismOutcome

-- §1 S-Expression (bit-for-bit compatible with `dump/Dump.hs` and `Code/SExpr.agda`)

inductive SExpr : Type where
  | sym  : String → SExpr
  | str  : String → SExpr
  | num  : Nat → SExpr
  | list : List SExpr → SExpr
  deriving Repr, BEq, Inhabited

private def escapeStr (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | '"' :: cs  => '\\' :: '"' :: go cs
    | '\\' :: cs => '\\' :: '\\' :: go cs
    | '\n' :: cs => '\\' :: 'n' :: go cs
    | '\r' :: cs => '\\' :: 'r' :: go cs
    | '\t' :: cs => '\\' :: 't' :: go cs
    | c :: cs    => c :: go cs
  String.ofList (go s.toList)

partial def renderSExpr : SExpr → String
  | .sym s   => s
  | .num n   => toString n
  | .str s   => "\"" ++ escapeStr s ++ "\""
  | .list xs => "(" ++ String.intercalate " " (xs.map renderSExpr) ++ ")"

def renderTopSExpr : SExpr → String
  | .list (.sym "module" :: nm :: ps :: ds) =>
      "(module " ++ renderSExpr nm ++ " " ++ renderSExpr ps ++ "\n" ++
      String.join (ds.map (fun d => "  " ++ renderSExpr d ++ "\n")) ++ ")"
  | s => renderSExpr s

-- §2 `Code` Abstract Syntax Tree (mirroring `Code.agda` 1-to-1)

structure QName : Type where
  full  : List String
  shown : String
  deriving Repr, BEq

def mkQ (xs : List String) : QName :=
  { full := xs, shown := xs.getLastD "" }

def fullDot (q : QName) : String :=
  String.intercalate "." q.full

inductive Hiding : Type where
  | visible | hidden | inst
  deriving Repr, BEq

structure Arg (α : Type) : Type where
  hid   : Hiding
  label : Option String
  thing : α
  deriving Repr, BEq

def visArg {α : Type} (x : α) : Arg α :=
  { hid := .visible, label := none, thing := x }

inductive Lit : Type where
  | natL  : Nat → Lit
  | strL  : String → Lit
  | charL : Char → Lit
  deriving Repr, BEq

inductive TermCheck : Type where
  | check | nonTerminating | terminating
  deriving Repr, BEq

structure Mods : Type where
  isPrivate  : Bool := false
  isInstance : Bool := false
  isAbstract : Bool := false
  termCheck  : TermCheck := .check
  deriving Repr, BEq

def plainMods : Mods := {}

structure Directive : Type where
  dusing    : Option (List String) := none
  dhiding   : List String := []
  drenaming : List (String × String) := []
  dpublic   : Bool := false
  deriving Repr, BEq

inductive Assoc : Type where
  | infixL | infixR | infixN
  deriving Repr, BEq

structure RecDir : Type where
  coind  : Bool := false
  constr : Option String := none
  deriving Repr, BEq

mutual
  inductive Expr : Type where
    | var       : String → Expr
    | def_      : QName → Expr
    | con       : QName → Expr
    | lit       : Lit → Expr
    | set       : Nat → Expr
    | hole      : Expr
    | meta_     : Expr
    | app       : Expr → Arg Expr → Expr
    | lam       : Arg String → Expr → Expr
    | lamT      : Bind → Expr → Expr
    | absurdLam : Hiding → Expr
    | lamCase   : List Clause → Expr
    | pi        : Bind → Expr → Expr
    | fun_      : Arg Expr → Expr → Expr
    | let_      : List LetBind → Expr → Expr
    | rec_      : List (String × Expr) → Expr
    | recUpd    : Expr → List (String × Expr) → Expr
    | dot       : Expr → Expr

  inductive Bind : Type where
    | bind : Hiding → List String → Expr → Bind

  inductive Pat : Type where
    | varP    : String → Pat
    | conP    : QName → List (Arg Pat) → Pat
    | wildP   : Pat
    | litP    : Lit → Pat
    | dotP    : Expr → Pat
    | absurdP : Pat
    | asP     : String → Pat → Pat
    | projP   : QName → Pat
    | recP    : List (String × Pat) → Pat

  inductive LHS : Type where
    | head  : QName → List (Arg Pat) → LHS
    | proj  : QName → LHS → List (Arg Pat) → LHS
    | with_ : LHS → List (Arg Pat) → List (Arg Pat) → LHS

  inductive RHS : Type where
    | rhs        : Expr → RHS
    | absurdRHS  : RHS
    | withRHS    : List Expr → List Clause → RHS
    | rewriteRHS : List Expr → RHS → RHS

  inductive Clause : Type where
    | clause : LHS → RHS → List Decl → Clause

  inductive LetBind : Type where
    | letBind : String → Expr → Expr → LetBind
    | letPat  : Pat → Expr → LetBind

  inductive Decl : Type where
    | pragma      : String → Decl
    | import_     : QName → Bool → Directive → List Decl → Decl
    | open_       : QName → Directive → Decl
    | fixity      : Assoc → Nat → String → Decl
    | sig         : Mods → String → Expr → Decl
    | fun_        : Mods → String → List Clause → Decl
    | dataSig     : Mods → String → List Bind → Expr → Decl
    | dataDef     : Mods → String → List String → List (String × Expr) → Decl
    | recSig      : Mods → String → List Bind → Expr → Decl
    | recDef      : Mods → String → List String → RecDir → List (String × Expr) → Decl
    | variable_   : List (String × Expr) → Decl
    | module_     : String → List Bind → List Decl → Decl
    | patSyn      : String → List String → Pat → Expr → Decl
    | unsupported : String → Decl
end

structure CodeMod : Type where
  modName : QName
  params  : List Bind
  decls   : List Decl

-- §3 Canonical S-Expr Encoder (exact mirror of `Code/Encode.agda` & `Dump.hs`)

def encQ (q : QName) : SExpr :=
  let f := fullDot q
  let last := q.full.getLastD ""
  if q.shown == last then .str f else .list [.sym "q", .str f, .str q.shown]

def encHid : Hiding → SExpr
  | .visible => .sym "vis"
  | .hidden  => .sym "hid"
  | .inst    => .sym "inst"

def encLabel : Option String → SExpr
  | none   => .sym "_"
  | some l => .str l

def encLit : Lit → SExpr
  | .natL n  => .list [.sym "nat", .num n]
  | .strL s  => .list [.sym "str", .str s]
  | .charL c => .list [.sym "chr", .str (String.singleton c)]

def encMods (m : Mods) : SExpr :=
  let p := if m.isPrivate then [.sym "private"] else []
  let i := if m.isInstance then [.sym "instance"] else []
  let a := if m.isAbstract then [.sym "abstract"] else []
  let t := match m.termCheck with
    | .check          => []
    | .nonTerminating => [.sym "nonterminating"]
    | .terminating    => [.sym "terminating"]
  .list (.sym "mods" :: (p ++ i ++ a ++ t))

def encAssoc : Assoc → SExpr
  | .infixL => .sym "l"
  | .infixR => .sym "r"
  | .infixN => .sym "n"

def encDir (d : Directive) : SExpr :=
  let u := match d.dusing with
    | none    => .sym "everything"
    | some ns => .list (.sym "using" :: ns.map .str)
  let h := .list (.sym "hiding" :: d.dhiding.map .str)
  let r := .list (.sym "renaming" :: d.drenaming.map (fun (a, b) => .list [.str a, .str b]))
  let pub := if d.dpublic then .sym "public" else .sym "private"
  .list [.sym "dir", u, h, r, pub]

mutual
  partial def encExpr : Expr → SExpr
    | .var x       => .list [.sym "var", .str x]
    | .def_ q      => .list [.sym "def", encQ q]
    | .con q       => .list [.sym "con", encQ q]
    | .lit l       => .list [.sym "lit", encLit l]
    | .set n       => .list [.sym "set", .num n]
    | .hole        => .sym "hole"
    | .meta_       => .sym "meta"
    | .app f a     => .list [.sym "app", encExpr f, encArg a]
    | .lam a e     => .list [.sym "lam", .list [.sym "arg", encHid a.hid, encLabel a.label, .str a.thing], encExpr e]
    | .lamT b e    => .list [.sym "lamT", encBind b, encExpr e]
    | .absurdLam h => .list [.sym "absurdlam", encHid h]
    | .lamCase cs  => .list (.sym "lamcase" :: cs.map encClause)
    | .pi b e      => .list [.sym "pi", encBind b, encExpr e]
    | .fun_ a e    => .list [.sym "fun", encArg a, encExpr e]
    | .let_ bs e   => .list [.sym "let", .list (bs.map encLetBind), encExpr e]
    | .rec_ fs     => .list [.sym "rec", .list (fs.map fun (n, e) => .list [.sym "fld", .str n, encExpr e])]
    | .recUpd r fs => .list [.sym "recupd", encExpr r, .list (fs.map fun (n, e) => .list [.sym "fld", .str n, encExpr e])]
    | .dot e       => .list [.sym "dot", encExpr e]

  partial def encArg (a : Arg Expr) : SExpr :=
    .list [.sym "arg", encHid a.hid, encLabel a.label, encExpr a.thing]

  partial def encBind : Bind → SExpr
    | .bind h xs t => .list [.sym "bind", encHid h, .list (xs.map .str), encExpr t]

  partial def encLetBind : LetBind → SExpr
    | .letBind x t e => .list [.sym "letbind", .str x, encExpr t, encExpr e]
    | .letPat p e    => .list [.sym "letpat", encPat p, encExpr e]

  partial def encPat : Pat → SExpr
    | .varP x    => .list [.sym "varp", .str x]
    | .conP q ps => .list (.sym "conp" :: encQ q :: ps.map encArgPat)
    | .wildP     => .sym "wildp"
    | .litP l    => .list [.sym "litp", encLit l]
    | .dotP e    => .list [.sym "dotp", encExpr e]
    | .absurdP   => .sym "absurdp"
    | .asP x p   => .list [.sym "asp", .str x, encPat p]
    | .projP q   => .list [.sym "projp", encQ q]
    | .recP fs   => .list [.sym "recp", .list (fs.map fun (n, p) => .list [.sym "fld", .str n, encPat p])]

  partial def encArgPat (a : Arg Pat) : SExpr :=
    .list [.sym "arg", encHid a.hid, encLabel a.label, encPat a.thing]

  partial def encLHS : LHS → SExpr
    | .head f ps     => .list (.sym "head" :: encQ f :: ps.map encArgPat)
    | .proj d l ps   => .list (.sym "proj" :: encQ d :: encLHS l :: ps.map encArgPat)
    | .with_ l ws ps => .list [.sym "with", encLHS l, .list (ws.map encArgPat), .list (ps.map encArgPat)]

  partial def encRHS : RHS → SExpr
    | .rhs e           => .list [.sym "rhs", encExpr e]
    | .absurdRHS       => .sym "absurdrhs"
    | .withRHS es cs   => .list [.sym "withrhs", .list (es.map encExpr), .list (cs.map encClause)]
    | .rewriteRHS es r => .list [.sym "rewriterhs", .list (es.map encExpr), encRHS r]

  partial def encClause : Clause → SExpr
    | .clause l r ws => .list [.sym "clause", encLHS l, encRHS r, .list (.sym "where" :: ws.map encDecl)]

  partial def encDecl : Decl → SExpr
    | .pragma s        => .list [.sym "pragma", .str s]
    | .import_ m o d a =>
        .list [.sym "import", encQ m, (if o then .sym "open" else .sym "noopen"), encDir d,
               .list (.sym "assumes" :: a.map encDecl)]
    | .open_ m d       => .list [.sym "open", encQ m, encDir d]
    | .fixity a n x    => .list [.sym "fixity", encAssoc a, .num n, .str x]
    | .sig m x e       => .list [.sym "sig", encMods m, .str x, encExpr e]
    | .fun_ m x cs     => .list (.sym "fun" :: encMods m :: .str x :: cs.map encClause)
    | .dataSig m x bs e => .list [.sym "datasig", encMods m, .str x, .list (.sym "params" :: bs.map encBind), encExpr e]
    | .dataDef m x ps cs =>
        .list (.sym "datadef" :: encMods m :: .str x :: .list (ps.map .str) ::
               cs.map fun (n, e) => .list [.sym "con", .str n, encExpr e])
    | .recSig m x bs e => .list [.sym "recsig", encMods m, .str x, .list (.sym "params" :: bs.map encBind), encExpr e]
    | .recDef m x ps rd fs =>
        let ind := if rd.coind then .sym "coinductive" else .sym "inductive"
        .list (.sym "recdef" :: encMods m :: .str x :: .list (ps.map .str) ::
               .list [.sym "recdir", ind, encLabel rd.constr] ::
               fs.map fun (n, e) => .list [.sym "field", .str n, encExpr e])
    | .variable_ vs    => .list (.sym "variable" :: vs.map fun (n, e) => .list [.sym "var", .str n, encExpr e])
    | .module_ x bs ds => .list (.sym "module" :: .str x :: .list (.sym "params" :: bs.map encBind) :: ds.map encDecl)
    | .patSyn x _ _ _  => .list [.sym "unsupported", .str ("pattern synonym " ++ x)]
    | .unsupported s   => .list [.sym "unsupported", .str s]
end

def encodeCodeMod (c : CodeMod) : SExpr :=
  .list (.sym "module" :: encQ c.modName :: .list (.sym "params" :: c.params.map encBind) :: c.decls.map encDecl)

partial def canonicalSExpr : SExpr → SExpr
  | .list [.sym "q", .str f, .str _] => .str f
  | .list xs => .list (xs.map canonicalSExpr)
  | x => x

def encodeCanonicalMod (c : CodeMod) : String :=
  renderSExpr (canonicalSExpr (encodeCodeMod c))

end Prism
