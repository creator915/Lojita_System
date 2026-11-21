module Code.PureCLI where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_; map; _++_; zip; upTo; length)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; unlines; intersperse) renaming (_++_ to _++ˢ_)
import Data.Nat.Show as ℕshow

open import Code
open import Code.Parse using (parse; parsePlan)
open import Code.Render using (render; chunksOf; depsOfChunk; dfsOrder; cycleMask; isHeader; lookupChunk; Chunk; cnames)
open import Code.Transport

parseCode : String → Maybe Code
parseCode = parse

renderCode : Code → String
renderCode = render

showObj : Obj → String
showObj (unit q) = intersperse "." (full q)
showObj (ext q)  = "⟨" ++ˢ intersperse "." (full q) ++ˢ "⟩"
showObj flags    = "flags"
showObj ⊥        = "⊥"

showCategory : Code → String
showCategory c = unlines (map showObj (objects c) ++ ("--- arrows (u → v : u 用到 v)" ∷ map arrow (arrows c)))
  where
    arrow : Obj × Obj → String
    arrow (u , v) = showObj u ++ˢ " → " ++ˢ showObj v

roundtripText : String → String
roundtripText txt = maybe′ renderCode "-- parse error" (parseCode txt)

unitsText : String → String
unitsText txt = maybe′ showCategory "-- parse error" (parseCode txt)

applyTexts : String → String → String
applyTexts old pl = go (parseCode old) (parsePlan pl)
  where
    showProb : Problem → String
    showProb (unknownSrc o)  = "源不在旧代码里: " ++ˢ showObj o
    showProb (unknownTgt o)  = "靶不在新代码里: " ++ˢ showObj o
    showProb (lostUnit o)    = "旧单元消失了但没有 proarrow 说它去了哪: " ++ˢ showObj o
    showProb (orphanUnit o)  = "新单元没有 proarrow 说它从哪来: " ++ˢ showObj o
    showProb (unsettled o)   = "义务没完成（它依赖的接口变了）: " ++ˢ showObj o
    showProb (dangling o q)  = "悬空引用: " ++ˢ showObj o ++ˢ " 用到 " ++ˢ intersperse "." (full q)

    go : Maybe Code → Maybe Plan → String
    go nothing  _        = "-- parse error (code)"
    go _        nothing  = "-- parse error (plan)"
    go (just c) (just p) =
      let c′ = apply p c
          ps = validate c p c′
      in unlines ( ("-- validate: " ++ˢ (if nullᵇ ps then "ok（这堆 proarrow 是 old ⇸ new 的一个 profunctor）" else "有问题"))
                 ∷ map (λ x → "--   " ++ˢ showProb x) ps
                 ++ ("-- 要唤醒的孩子: " ++ˢ intersperse " " (map (λ m → intersperse "." (full m)) (affectedChildren c′ p)))
                 ∷ "" ∷ renderCode c′ ∷ [])

orderText : String → String
orderText txt = maybe′ showOrder "-- parse error" (parseCode txt)
  where
    showOrder : Code → String
    showOrder c =
      let body  = filterᵇ (λ d → not (isHeader d)) (decls c)
          cs    = chunksOf (full (modName c)) body
          res   = resolveIn (modName c) (units c) (extUnits c)
          deps  = λ i → maybe′ (depsOfChunk res cs) [] (lookupChunk cs i)
          order = dfsOrder deps (length cs)
          mask  = cycleMask deps order
      in unlines (map (λ im → (if proj₂ im then "CYCLE " else "      ") ++ˢ ℕshow.show (proj₁ im) ++ˢ " "
                               ++ˢ maybe′ (λ k → intersperse "," (map (λ q → intersperse "." (full q)) (cnames k))) "?" (lookupChunk cs (proj₁ im))
                               ++ˢ "  deps=" ++ˢ intersperse "," (map ℕshow.show (deps (proj₁ im))))
                      (zip order mask))
