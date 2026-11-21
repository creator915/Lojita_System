module Code.PlanPreview where

open import Data.Bool using (true; false; if_then_else_; not)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat using (ℕ; _<ᵇ_; _+_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; intersperse; toList; fromList) renaming (_++_ to _++ˢ_)
import Data.Char as C

open import Code
open import Code.Encode
open import Code.Parse
open import Code.Protocol
open import Code.Transport
open import Code.Lift
open import Code.HarnessCore
open import Code.Render using (render)
open import Code.Prompt using (showImplProblem; showLiftProblem)
open import Code.SExpr using (SExpr; list; sym; str; showSExpr; parseSExpr)
import Code.Submission as Sub
import Code.NodeTransport as NT
import Code.PolyTransport as PT

private
  infixl 1 _>>=_
  _>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= f = nothing
  just x >>= f = f x

  items : ∀ {A : Set} → (SExpr → Maybe A) → List SExpr → Maybe (List A)
  items f [] = just []
  items f (x ∷ xs) = f x >>= λ a → items f xs >>= λ as → just (a ∷ as)

  tagged : String → List SExpr → SExpr
  tagged k xs = list (sym k ∷ xs)

  encMove : Proarrow → SExpr
  encMove (a ⇝ b) = tagged "move" (encObj a ∷ encObj b ∷ [])

  encFrozen : NT.Frozen → SExpr
  encFrozen (NT.frozen c _ ds cs) = list (encodeCode c ∷ encodeDecls ds ∷ list (kids cs) ∷ [])
    where
      kids : List (Name × NT.Frozen) → List SExpr
      kids [] = []
      kids ((n , h) ∷ rest) = list (str n ∷ encFrozen h ∷ []) ∷ kids rest

  decFrozen : SExpr → Maybe NT.Frozen
  decFrozen (list (m ∷ ds ∷ list cs ∷ [])) =
    decodeCode m >>= λ c → decodeDeclList ds >>= λ iface → kids cs >>= λ children →
    just (NT.frozen c [] iface children)
    where
      kids : List SExpr → Maybe (List (Name × NT.Frozen))
      kids [] = just []
      kids (list (str n ∷ h ∷ []) ∷ rest) = decFrozen h >>= λ v → kids rest >>= λ vs → just ((n , v) ∷ vs)
      kids _ = nothing
  decFrozen _ = nothing

  encBinding : NT.Frozen × PT.TransportSpec → SExpr
  encBinding (h , s) = list (encFrozen h ∷ PT.encodePolyTransport s ∷ [])

  decBinding : SExpr → Maybe (NT.Frozen × PT.TransportSpec)
  decBinding (list (h ∷ s ∷ [])) = decFrozen h >>= λ v → PT.decodePolyTransport s >>= λ t → just (v , t)
  decBinding _ = nothing

  decAncestors : List SExpr → Maybe (Maybe (List QName))
  decAncestors (sym "none" ∷ []) = just nothing
  decAncestors xs = items decodeQ xs >>= λ qs → just (just qs)

  decLiftBase : List SExpr → Maybe (Maybe (Code × LiftSpec))
  decLiftBase [] = just nothing
  decLiftBase (b ∷ l ∷ []) = decodeCode b >>= λ c → decodeLift l >>= λ spec → just (just (c , spec))
  decLiftBase _ = nothing

  existingDeps : NodeTask → Code → List Code
  existingDeps t old = nodeDeps t (map (λ { (q , ds) → stubOf (specΔ q ds []) }) (candidateInterfaces t old []))

-- Only the parent stages this snapshot. It includes exactly the inputs of the
-- structural gates. Live channels, thread IDs and frozen subtree memories do
-- not participate. Authored views are retained only for actual scope deps.
planContext : NodeTask → Code → List QName → String
planContext t old siblings = showSExpr (tagged "plan-context"
  (encodeCode old ∷ encodeCode (code (child d) [] (newIface d))
  ∷ tagged "seeds" (map encMove (δarrows d)) ∷ tagged "flags" (map str (parentFlags t))
  ∷ tagged "ancestors" (maybe′ (map encQ) (sym "none" ∷ []) (allowedAncestors t))
  ∷ tagged "bases" (map encodeCode (baseModules t))
  ∷ tagged "lift" (maybe′ (λ { (b , l) → encodeCode b ∷ encodeLift l ∷ [] }) [] (maybeLift t))
  ∷ tagged "bindings" (map encBinding (transports t)) ∷ tagged "siblings" (map encQ siblings)
  ∷ tagged "sources" (concatMap authored (existingDeps t old)) ∷ []))
  where
    d = δ t
    authored : Code → List SExpr
    authored c with authoredSurface (authoredSources t) c
    ... | nothing = []
    ... | just src = list (str (NT.moduleKey (modName c)) ∷ str src ∷ []) ∷ []

private
  record Snapshot : Set where
    constructor snapshot
    field
      task : NodeTask
      old : Code
      siblings : List QName
      sources : List (String × String)

  decSources : List SExpr → Maybe (List (Name × String))
  decSources [] = just []
  decSources (list (sym "sources" ∷ xs) ∷ []) = Sub.decodeSubspecs xs
  decSources _ = nothing

  decContext : SExpr → Maybe Snapshot
  decContext (list (sym "plan-context" ∷ old ∷ spec ∷ list (sym "seeds" ∷ seeds) ∷ list (sym "flags" ∷ fs)
    ∷ list (sym "ancestors" ∷ as) ∷ list (sym "bases" ∷ bs) ∷ list (sym "lift" ∷ l)
    ∷ list (sym "bindings" ∷ ts) ∷ list (sym "siblings" ∷ ss) ∷ surfaces)) =
    decodeCode old >>= λ c → decodeCode spec >>= λ s → decodeMoves seeds >>= λ ms →
    decodeNames fs >>= λ opts → decAncestors as >>= λ ancestors → items decodeCode bs >>= λ bases →
    decLiftBase l >>= λ vertical → items decBinding ts >>= λ horizontal → items decodeQ ss >>= λ siblings →
    decSources surfaces >>= λ raw →
    just (snapshot (record (nodeTask (specΔ (modName s) (decls s) ms) opts vertical)
      { baseModules = bases ; transports = horizontal ; allowedAncestors = ancestors }) c siblings raw)
  decContext _ = nothing

  record Request : Set where
    constructor request
    field
      moves : List Proarrow
      main : Code
      subs : List (String × Code)
      extraLift : Maybe LiftSpec

  decChild : SExpr → Maybe (String × Code)
  decChild (list (str n ∷ m ∷ [])) = decodeCode m >>= λ c → just (n , c)
  decChild _ = nothing

  decExtra : List SExpr → Maybe (Maybe LiftSpec)
  decExtra [] = just nothing
  decExtra (x ∷ []) = decodeLift x >>= λ l → just (just l)
  decExtra _ = nothing

  decRequest : SExpr → Maybe Request
  decRequest (list (sym "check-plan" ∷ list (sym "moves" ∷ ms) ∷ main ∷ list (sym "subspecs" ∷ ss) ∷ list (sym "lift" ∷ l) ∷ [])) =
    decodeMoves ms >>= λ moves → decodeCode main >>= λ c → items decChild ss >>= λ subs →
    decExtra l >>= λ extra → just (request moves c subs extra)
  decRequest _ = nothing

  -- Every diagnostic is user data. Escape all JSON control characters,
  -- including control bytes inside valid source literals.
  hex : ℕ → C.Char
  hex n = C.fromℕ (if n <ᵇ 10 then 48 + n else 87 + n)

  escapeChar : C.Char → List C.Char
  escapeChar '"' = '\\' ∷ '"' ∷ []
  escapeChar '\\' = '\\' ∷ '\\' ∷ []
  escapeChar c = if n <ᵇ 32 then '\\' ∷ 'u' ∷ '0' ∷ '0' ∷ (if n <ᵇ 16 then '0' else '1') ∷ hex (if n <ᵇ 16 then n else n ∸ 16) ∷ [] else c ∷ []
    where n = C.toℕ c

  jsonString : String → String
  jsonString s = "\"" ++ˢ fromList (concatMap escapeChar (toList s)) ++ˢ "\""

  array : List String → String
  array xs = "[" ++ˢ intersperse "," xs ++ˢ "]"

  jsonCert : NarrowingCertificate → String
  jsonCert (certificate k w c d) = "{\"kind\":" ++ˢ jsonString k ++ˢ ",\"witness\":" ++ˢ jsonString w
    ++ˢ ",\"cause\":" ++ˢ jsonString c ++ˢ ",\"detour\":" ++ˢ jsonString d ++ˢ "}"

  report : List String → List NarrowingCertificate → List Obj → List String → Maybe Code → String
  report errors certs front details candidate = "{\"ok\":" ++ˢ (if nullᵇ errors then "true" else "false")
    ++ˢ ",\"diagnostics\":" ++ˢ array (map jsonString errors) ++ˢ ",\"certificates\":" ++ˢ array (map jsonCert certs)
    ++ˢ ",\"frontier\":" ++ˢ array (map (λ o → jsonString (showSExpr (encObj o))) front)
    ++ˢ ",\"satisfiesDetails\":" ++ˢ array (map jsonString details)
    ++ˢ maybe′ (λ c → ",\"candidateCode\":" ++ˢ jsonString (showSExpr (encodeCode c))) "" candidate ++ˢ "}"

  message : ∀ {A : Set} → Maybe A → List A
  message nothing = []
  message (just x) = x ∷ []

  failure : String → String
  failure s = report (s ∷ []) [] [] [] nothing

  unsafeProblems : List ImplProblem → List NarrowingCertificate
  unsafeProblems = concatMap describe
    where
      describe : ImplProblem → List NarrowingCertificate
      describe (unsafePrimitive q) = unsafeCertificate (NT.moduleKey q) ∷ []
      describe _ = []

  objectErrors : String → List String → Code → List String
  objectErrors role opts c = map showImplProblem impl ++ (if role ==ˢ "closed" then [] else message (specProblem (decls c)))
    ++ (if role ==ˢ "subspec" then map proj₂ (message (subspecNarrowingProblem c)) else [])
    where impl = if role ==ˢ "closed" then closedImplOK opts c else specImplOK opts c

  objectCerts : String → List String → Code → List NarrowingCertificate
  objectCerts role opts c = unsafeProblems (specImplOK opts c) ++ (if role ==ˢ "subspec" then subspecCertificates c else [])

  extraProblems : NodeTask → Code → Maybe LiftSpec → List String
  extraProblems t c nothing = []
  extraProblems t c (just l) with NT.findCode (baseMod l) (baseModules t ++ map proj₁ (message (maybeLift t)))
  ... | nothing = ("checkLift: unknown base " ++ˢ NT.moduleKey (baseMod l)) ∷ []
  ... | just b = map showLiftProblem (liftProblems (record t { maybeLift = just (b , l) }) c)

  preview : Snapshot → Request → String
  preview (snapshot t old slots _) (request ms main subs lift) =
    report errors certs front (map (λ m → InterfaceMismatch.summary m ++ˢ InterfaceMismatch.detail m) mismatches) (just (withTests cand (newIface (δ t))))
    where
      names = map (λ e → NT.moduleQName (proj₁ e)) subs
      siblings = names ++ filterᵇ (λ q → not (elemᵇ _==ᴺ_ q names)) slots
      childErrors : String × Code → List String
      childErrors (n , c) = objectErrors "subspec" (parentFlags t) c ++ message (subspecBoundaryProblem t siblings c)
        ++ (if NT.moduleKey (modName c) ==ˢ n then [] else ("subspec module name differs from its key: " ++ˢ n) ∷ [])
      merged = candidateInterfaces t old (map (λ { (_ , c) → modName c , decls c }) subs)
      p = candidatePlan t "preview" main merged ms
      cand = apply p old
      front = frontier old cand p
      mismatches = satisfiesMismatches (δ t) cand
      errors = (if modName main ==ᴺ child (δ t) then [] else "main: module name differs from assigned ownership node" ∷ [])
        ++ concatMap childErrors subs ++ message (checkCandidateGates t old p cand) ++ extraProblems t cand lift
      certs = concatMap (λ e → objectCerts "subspec" (parentFlags t) (proj₂ e)) subs
        ++ unsafeProblems (closedImplOK (parentFlags t) cand) ++ frontierCertificates old cand p front ++ map interfaceCertificate mismatches

planPreview : String → String → String
planPreview ctx req with parseSExpr ctx >>= decContext | parseSExpr req >>= decRequest
... | nothing | _ = failure "invalid parent plan context"
... | _ | nothing = failure "invalid plan request"
... | just context | just proposal = preview context proposal

objectPreview : String → List String → String → String
objectPreview role opts txt with parse txt
... | nothing = failure "invalid candidate"
... | just c = report (objectErrors role opts c) (objectCerts role opts c) [] [] nothing

interfacePreview : String → String → String
interfacePreview sp ca with parse sp | parse ca
... | just s | just c = let d = specΔ (modName s) (decls s) []
                            ms = satisfiesMismatches d c
                            ds = satisfiesDetails d c
                        in report (if satisfies d c then [] else "INTERFACE_MISMATCH" ∷ ds) (map interfaceCertificate ms) [] ds nothing
... | _ | _ = failure "invalid specification or candidate"

decodePlanSource : String → String
decodePlanSource txt with Sub.parseSubmission txt
... | just (Sub.submitPlan _ main subs ms) = "{\"main\":" ++ˢ jsonString main ++ˢ ",\"moves\":" ++ˢ jsonString (showSExpr (tagged "moves" (map encMove ms)))
  ++ˢ ",\"subspecs\":" ++ˢ array (map (λ { (n , s) → array (jsonString n ∷ jsonString s ∷ []) }) subs) ++ˢ "}"
... | just (Sub.refuteLift _ _) = failure "Use check_agda with refute_lift=true to check a refute-lift witness."
... | _ = failure ("expected a plan submission: " ++ˢ Sub.explainSubmissionFailure txt)

private
  decSubs : SExpr → Maybe (List (Name × Code))
  decSubs (list (sym "subspecs" ∷ xs)) = items decChild xs
  decSubs _ = nothing

planDeps : String → String → String
planDeps ctx supplied with parseSExpr ctx >>= decContext | parseSExpr supplied >>= decSubs
... | just (snapshot t old _ raw) | just subs = array (map depSource deps)
  where
    ifaces = map (λ { (_ , c) → modName c , decls c }) subs
    deps = nodeDeps t (map (λ { (q , ds) → stubOf (specΔ q ds []) }) (candidateInterfaces t old ifaces))
    submitted = map proj₁ subs
    depSource : Code → String
    depSource c = array (jsonString n ∷ jsonString (if surface ==ˢ "" then render c else surface) ∷ [])
      where
        n = NT.moduleKey (modName c)
        surface = if elemᵇ _==ˢ_ n submitted then "" else lookupRawSubspec raw n
... | _ | _ = failure "invalid parent plan context or subspecs"
