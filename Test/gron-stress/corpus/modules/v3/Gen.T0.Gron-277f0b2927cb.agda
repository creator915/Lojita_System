module Gen.T0.Gron where

  open import Agda.Builtin.Char using (primNatToChar)
  open import Agda.Builtin.Char using (Char; primCharToNat; primIsAlpha)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (Bool; true; false)
  open import Data.Bool using (not; _∧_; _∨_; if_then_else_)
  open import Data.List using (List; []; _∷_; _++_; map; upTo)
  open import Data.List using (any; all; concat; reverse; foldl)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ)
  open import Data.Nat using (zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_)
  open import Data.Product using (_×_; _,_)
  open import Data.Product using (proj₁; proj₂)
  open import Data.String using (String; fromList)
  open import Data.String using (toList)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Bool using (Bool; true; false)
  open import Data.Bool using (not; _∧_; _∨_; if_then_else_)
  open import Data.List using (List; []; _∷_; _++_; map; upTo)
  open import Data.List using (any; all; concat; reverse; foldl)
  open import Data.Nat using (ℕ)
  open import Data.Nat using (zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_)
  open import Data.Product using (_×_; _,_)
  open import Data.Product using (proj₁; proj₂)
  open import Data.String using (String; fromList)
  open import Data.String using (toList)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Binary.PropositionalEquality using (refl)
  data Mode : Set where
    gronMode : Mode
    ungronMode : Mode
    valuesMode : Mode
  record ModeFlags : Set where
    constructor modeFlags
    field
      ungronRequested : Bool
      valuesRequested : Bool
  data StdoutAttachment : Set where
    stdoutPipe : StdoutAttachment
    stdoutTTY : StdoutAttachment
  data Style : Set where
    plain : Style
    ansi : Style
  record ColorFlags : Set where
    constructor colorFlags
    field
      colorRequested : Bool
      monochromeRequested : Bool
      stdoutAttachment : StdoutAttachment
  data JSON : Set where
    jNull : JSON
    jBool : Bool → JSON
    jNumber : String → JSON
    jString : String → JSON
    jArray : List JSON → JSON
    jObject : List (String × JSON) → JSON
  data Segment : Set where
    key : String → Segment
    index : ℕ → Segment
  record Statement : Set where
    constructor statement
    field
      path : List Segment
      value : JSON
  data KeyNotation : Set where
    dotted : KeyNotation
    bracketed : KeyNotation
  data SortMode : Set where
    sortPaths : SortMode
    skipSort : SortMode
  selectMode : ModeFlags → Mode
  selectMode (modeFlags true _) = ungronMode
  selectMode (modeFlags false true) = valuesMode
  selectMode (modeFlags false false) = gronMode
  selectStyle : ColorFlags → Style
  selectStyle (colorFlags true _ _) = ansi
  selectStyle (colorFlags false true _) = plain
  selectStyle (colorFlags false false stdoutPipe) = plain
  selectStyle (colorFlags false false stdoutTTY) = ansi
  private
    inRanges : ℕ → List (ℕ × ℕ) → Bool
    inRanges n [] = false
    inRanges n ((lo , hi) ∷ rest) = if (n <ᵇ lo) then false else (if (hi <ᵇ n) then inRanges n rest else true)
  private
    letterNumbers : List (ℕ × ℕ)
    letterNumbers = (5870 , 5872) ∷ ((8544 , 8578) ∷ ((8581 , 8584) ∷ ((12295 , 12295) ∷ ((12321 , 12329) ∷ ((12344 , 12346) ∷ ((42726 , 42735) ∷ ((65856 , 65908) ∷ ((66369 , 66369) ∷ ((66378 , 66378) ∷ ((66513 , 66517) ∷ ((74752 , 74862) ∷ [])))))))))))
  private
    decimalStarts : List ℕ
    decimalStarts = 48 ∷ (1632 ∷ (1776 ∷ (1984 ∷ (2406 ∷ (2534 ∷ (2662 ∷ (2790 ∷ (2918 ∷ (3046 ∷ (3174 ∷ (3302 ∷ (3430 ∷ (3558 ∷ (3664 ∷ (3792 ∷ (3872 ∷ (4160 ∷ (4240 ∷ (6112 ∷ (6160 ∷ (6470 ∷ (6608 ∷ (6784 ∷ (6800 ∷ (6992 ∷ (7088 ∷ (7232 ∷ (7248 ∷ (42528 ∷ (43216 ∷ (43264 ∷ (43472 ∷ (43504 ∷ (43600 ∷ (44016 ∷ (65296 ∷ (66720 ∷ (68912 ∷ (69734 ∷ (69872 ∷ (69942 ∷ (70096 ∷ (70384 ∷ (70736 ∷ (70864 ∷ (71248 ∷ (71360 ∷ (71472 ∷ (71904 ∷ (72016 ∷ (72784 ∷ (73040 ∷ (73120 ∷ (73552 ∷ (92768 ∷ (92864 ∷ (93008 ∷ (120782 ∷ (120792 ∷ (120802 ∷ (120812 ∷ (120822 ∷ (123200 ∷ (123632 ∷ (124144 ∷ (125264 ∷ (130032 ∷ [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  private
    identifierTailRanges : List (ℕ × ℕ)
    identifierTailRanges = (768 , 879) ∷ ((1155 , 1159) ∷ ((1425 , 1469) ∷ ((1471 , 1471) ∷ ((1473 , 1474) ∷ ((1476 , 1477) ∷ ((1479 , 1479) ∷ ((1552 , 1562) ∷ ((1611 , 1631) ∷ ((1648 , 1648) ∷ ((1750 , 1756) ∷ ((1759 , 1764) ∷ ((1767 , 1768) ∷ ((1770 , 1773) ∷ ((1809 , 1809) ∷ ((1840 , 1866) ∷ ((1958 , 1968) ∷ ((2027 , 2035) ∷ ((2045 , 2045) ∷ ((2070 , 2073) ∷ ((2075 , 2083) ∷ ((2085 , 2087) ∷ ((2089 , 2093) ∷ ((2137 , 2139) ∷ ((2200 , 2207) ∷ ((2250 , 2273) ∷ ((2275 , 2307) ∷ ((2362 , 2364) ∷ ((2366 , 2383) ∷ ((2385 , 2391) ∷ ((2402 , 2403) ∷ ((2433 , 2435) ∷ ((2492 , 2492) ∷ ((2494 , 2500) ∷ ((2503 , 2504) ∷ ((2507 , 2509) ∷ ((2519 , 2519) ∷ ((2530 , 2531) ∷ ((2558 , 2558) ∷ ((2561 , 2563) ∷ ((2620 , 2620) ∷ ((2622 , 2626) ∷ ((2631 , 2632) ∷ ((2635 , 2637) ∷ ((2641 , 2641) ∷ ((2672 , 2673) ∷ ((2677 , 2677) ∷ ((2689 , 2691) ∷ ((2748 , 2748) ∷ ((2750 , 2757) ∷ ((2759 , 2761) ∷ ((2763 , 2765) ∷ ((2786 , 2787) ∷ ((2810 , 2815) ∷ ((2817 , 2819) ∷ ((2876 , 2876) ∷ ((2878 , 2884) ∷ ((2887 , 2888) ∷ ((2891 , 2893) ∷ ((2901 , 2903) ∷ ((2914 , 2915) ∷ ((2946 , 2946) ∷ ((3006 , 3010) ∷ ((3014 , 3016) ∷ ((3018 , 3021) ∷ ((3031 , 3031) ∷ ((3072 , 3076) ∷ ((3132 , 3132) ∷ ((3134 , 3140) ∷ ((3142 , 3144) ∷ ((3146 , 3149) ∷ ((3157 , 3158) ∷ ((3170 , 3171) ∷ ((3201 , 3203) ∷ ((3260 , 3260) ∷ ((3262 , 3268) ∷ ((3270 , 3272) ∷ ((3274 , 3277) ∷ ((3285 , 3286) ∷ ((3298 , 3299) ∷ ((3315 , 3315) ∷ ((3328 , 3331) ∷ ((3387 , 3388) ∷ ((3390 , 3396) ∷ ((3398 , 3400) ∷ ((3402 , 3405) ∷ ((3415 , 3415) ∷ ((3426 , 3427) ∷ ((3457 , 3459) ∷ ((3530 , 3530) ∷ ((3535 , 3540) ∷ ((3542 , 3542) ∷ ((3544 , 3551) ∷ ((3570 , 3571) ∷ ((3633 , 3633) ∷ ((3636 , 3642) ∷ ((3655 , 3662) ∷ ((3761 , 3761) ∷ ((3764 , 3772) ∷ ((3784 , 3790) ∷ ((3864 , 3865) ∷ ((3893 , 3893) ∷ ((3895 , 3895) ∷ ((3897 , 3897) ∷ ((3902 , 3903) ∷ ((3953 , 3972) ∷ ((3974 , 3975) ∷ ((3981 , 3991) ∷ ((3993 , 4028) ∷ ((4038 , 4038) ∷ ((4139 , 4158) ∷ ((4182 , 4185) ∷ ((4190 , 4192) ∷ ((4194 , 4196) ∷ ((4199 , 4205) ∷ ((4209 , 4212) ∷ ((4226 , 4237) ∷ ((4239 , 4239) ∷ ((4250 , 4253) ∷ ((4957 , 4959) ∷ ((5906 , 5909) ∷ ((5938 , 5940) ∷ ((5970 , 5971) ∷ ((6002 , 6003) ∷ ((6068 , 6099) ∷ ((6109 , 6109) ∷ ((6155 , 6157) ∷ ((6159 , 6159) ∷ ((6277 , 6278) ∷ ((6313 , 6313) ∷ ((6432 , 6443) ∷ ((6448 , 6459) ∷ ((6679 , 6683) ∷ ((6741 , 6750) ∷ ((6752 , 6780) ∷ ((6783 , 6783) ∷ ((6832 , 6845) ∷ ((6847 , 6862) ∷ ((6912 , 6916) ∷ ((6964 , 6980) ∷ ((7019 , 7027) ∷ ((7040 , 7042) ∷ ((7073 , 7085) ∷ ((7142 , 7155) ∷ ((7204 , 7223) ∷ ((7376 , 7378) ∷ ((7380 , 7400) ∷ ((7405 , 7405) ∷ ((7412 , 7412) ∷ ((7415 , 7417) ∷ ((7616 , 7679) ∷ ((8255 , 8256) ∷ ((8276 , 8276) ∷ ((8400 , 8412) ∷ ((8417 , 8417) ∷ ((8421 , 8432) ∷ ((11503 , 11505) ∷ ((11647 , 11647) ∷ ((11744 , 11775) ∷ ((12330 , 12335) ∷ ((12441 , 12442) ∷ ((42607 , 42607) ∷ ((42612 , 42621) ∷ ((42654 , 42655) ∷ ((42736 , 42737) ∷ ((43010 , 43010) ∷ ((43014 , 43014) ∷ ((43019 , 43019) ∷ ((43043 , 43047) ∷ ((43052 , 43052) ∷ ((43136 , 43137) ∷ ((43188 , 43205) ∷ ((43232 , 43249) ∷ ((43263 , 43263) ∷ ((43302 , 43309) ∷ ((43335 , 43347) ∷ ((43392 , 43395) ∷ ((43443 , 43456) ∷ ((43493 , 43493) ∷ ((43561 , 43574) ∷ ((43587 , 43587) ∷ ((43596 , 43597) ∷ ((43643 , 43645) ∷ ((43696 , 43696) ∷ ((43698 , 43700) ∷ ((43703 , 43704) ∷ ((43710 , 43711) ∷ ((43713 , 43713) ∷ ((43755 , 43759) ∷ ((43765 , 43766) ∷ ((44003 , 44010) ∷ ((44012 , 44013) ∷ ((64286 , 64286) ∷ ((65024 , 65039) ∷ ((65056 , 65071) ∷ ((65075 , 65076) ∷ ((65101 , 65103) ∷ ((65343 , 65343) ∷ ((66045 , 66045) ∷ ((66272 , 66272) ∷ ((66422 , 66426) ∷ ((68097 , 68099) ∷ ((68101 , 68102) ∷ ((68108 , 68111) ∷ ((68152 , 68154) ∷ ((68159 , 68159) ∷ ((68325 , 68326) ∷ ((68900 , 68903) ∷ ((69291 , 69292) ∷ ((69373 , 69375) ∷ ((69446 , 69456) ∷ ((69506 , 69509) ∷ ((69632 , 69634) ∷ ((69688 , 69702) ∷ ((69744 , 69744) ∷ ((69747 , 69748) ∷ ((69759 , 69762) ∷ ((69808 , 69818) ∷ ((69826 , 69826) ∷ ((69888 , 69890) ∷ ((69927 , 69940) ∷ ((69957 , 69958) ∷ ((70003 , 70003) ∷ ((70016 , 70018) ∷ ((70067 , 70080) ∷ ((70089 , 70092) ∷ ((70094 , 70095) ∷ ((70188 , 70199) ∷ ((70206 , 70206) ∷ ((70209 , 70209) ∷ ((70367 , 70378) ∷ ((70400 , 70403) ∷ ((70459 , 70460) ∷ ((70462 , 70468) ∷ ((70471 , 70472) ∷ ((70475 , 70477) ∷ ((70487 , 70487) ∷ ((70498 , 70499) ∷ ((70502 , 70508) ∷ ((70512 , 70516) ∷ ((70709 , 70726) ∷ ((70750 , 70750) ∷ ((70832 , 70851) ∷ ((71087 , 71093) ∷ ((71096 , 71104) ∷ ((71132 , 71133) ∷ ((71216 , 71232) ∷ ((71339 , 71351) ∷ ((71453 , 71467) ∷ ((71724 , 71738) ∷ ((71984 , 71989) ∷ ((71991 , 71992) ∷ ((71995 , 71998) ∷ ((72000 , 72000) ∷ ((72002 , 72003) ∷ ((72145 , 72151) ∷ ((72154 , 72160) ∷ ((72164 , 72164) ∷ ((72193 , 72202) ∷ ((72243 , 72249) ∷ ((72251 , 72254) ∷ ((72263 , 72263) ∷ ((72273 , 72283) ∷ ((72330 , 72345) ∷ ((72751 , 72758) ∷ ((72760 , 72767) ∷ ((72850 , 72871) ∷ ((72873 , 72886) ∷ ((73009 , 73014) ∷ ((73018 , 73018) ∷ ((73020 , 73021) ∷ ((73023 , 73029) ∷ ((73031 , 73031) ∷ ((73098 , 73102) ∷ ((73104 , 73105) ∷ ((73107 , 73111) ∷ ((73459 , 73462) ∷ ((73472 , 73473) ∷ ((73475 , 73475) ∷ ((73524 , 73530) ∷ ((73534 , 73538) ∷ ((78912 , 78912) ∷ ((78919 , 78933) ∷ ((92912 , 92916) ∷ ((92976 , 92982) ∷ ((94031 , 94031) ∷ ((94033 , 94087) ∷ ((94095 , 94098) ∷ ((94180 , 94180) ∷ ((94192 , 94193) ∷ ((113821 , 113822) ∷ ((118528 , 118573) ∷ ((118576 , 118598) ∷ ((119141 , 119145) ∷ ((119149 , 119154) ∷ ((119163 , 119170) ∷ ((119173 , 119179) ∷ ((119210 , 119213) ∷ ((119362 , 119364) ∷ ((121344 , 121398) ∷ ((121403 , 121452) ∷ ((121461 , 121461) ∷ ((121476 , 121476) ∷ ((121499 , 121503) ∷ ((121505 , 121519) ∷ ((122880 , 122886) ∷ ((122888 , 122904) ∷ ((122907 , 122913) ∷ ((122915 , 122916) ∷ ((122918 , 122922) ∷ ((123023 , 123023) ∷ ((123184 , 123190) ∷ ((123566 , 123566) ∷ ((123628 , 123631) ∷ ((124140 , 124143) ∷ ((125136 , 125142) ∷ ((125252 , 125258) ∷ ((917760 , 917999) ∷ [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  private
    identifierStart : Char → Bool
    identifierStart c = let n = primCharToNat c in (n ≡ᵇ 36) ∨ ((n ≡ᵇ 95) ∨ (primIsAlpha c ∨ inRanges n letterNumbers))
  private
    identifierTail : Char → Bool
    identifierTail c = let n = primCharToNat c in identifierStart c ∨ (any (λ start → not (n <ᵇ start) ∧ (n <ᵇ (start + 10))) decimalStarts ∨ inRanges n identifierTailRanges)
  private
    reserved : String → Bool
    reserved name = any (primStringEquality name) ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  keyNotation : String → KeyNotation
  keyNotation name with toList name
  keyNotation name | [] = bracketed
  keyNotation name | (c ∷ cs) = if (identifierStart c ∧ (all identifierTail cs ∧ not (reserved name))) then dotted else bracketed
  private
    keyEscapes : List (ℕ × String)
    keyEscapes = (34 , "\\\"") ∷ ((92 , "\\\\") ∷ ((8 , "\\b") ∷ ((9 , "\\t") ∷ ((10 , "\\n") ∷ ((12 , "\\f") ∷ ((13 , "\\r") ∷ ((38 , "\\u0026") ∷ ((60 , "\\u003c") ∷ ((62 , "\\u003e") ∷ ((8232 , "\\u2028") ∷ ((8233 , "\\u2029") ∷ [])))))))))))
  private
    findEscape : ℕ → List (ℕ × String) → Maybe String
    findEscape n [] = nothing
    findEscape n ((code , text) ∷ rest) = if (n ≡ᵇ code) then just text else findEscape n rest
  private
    hexDigit : ℕ → Char
    hexDigit n = primNatToChar (if (n <ᵇ 10) then (48 + n) else (87 + n))
  private
    controlEscape : ℕ → List Char
    controlEscape n = '\\' ∷ ('u' ∷ ('0' ∷ ('0' ∷ ((if (n <ᵇ 16) then '0' else '1') ∷ (hexDigit (if (n <ᵇ 16) then n else (n ∸ 16)) ∷ [])))))
  private
    escapeCharacter : Char → List Char
    escapeCharacter c with findEscape (primCharToNat c) keyEscapes
    escapeCharacter c | (just text) = toList text
    escapeCharacter c | nothing = if (primCharToNat c <ᵇ 32) then controlEscape (primCharToNat c) else (c ∷ [])
  private
    quotedTail : List Char → List Char
    quotedTail [] = '\"' ∷ (']' ∷ [])
    quotedTail (c ∷ cs) = escapeCharacter c ++ quotedTail cs
  private
    keySortForm : String → String
    keySortForm name with keyNotation name
    keySortForm name | dotted = fromList ('.' ∷ toList name)
    keySortForm name | bracketed = fromList ('[' ∷ ('\"' ∷ quotedTail (toList name)))
  private
    lessChars : List Char → List Char → Bool
    lessChars [] [] = false
    lessChars [] (_ ∷ _) = true
    lessChars (_ ∷ _) [] = false
    lessChars (c ∷ cs) (d ∷ ds) with (primCharToNat c ≡ᵇ primCharToNat d)
    lessChars (c ∷ cs) (d ∷ ds) | true = lessChars cs ds
    lessChars (c ∷ cs) (d ∷ ds) | false = primCharToNat c <ᵇ primCharToNat d
  private
    alterSorted : {A : Set} → String → A → (A → A) → List (String × A) → List (String × A)
    alterSorted name initial update [] = (name , initial) ∷ []
    alterSorted name initial update ((k , v) ∷ rest) = if primStringEquality name k then ((k , update v) ∷ rest) else (if lessChars (toList name) (toList k) then ((name , initial) ∷ ((k , v) ∷ rest)) else ((k , v) ∷ alterSorted name initial update rest))
  private
    keepMember : SortMode → String → List Statement → List (String × List Statement) → List (String × List Statement)
    keepMember sortPaths name body rest = alterSorted (keySortForm name) body (λ old → old) rest
    keepMember skipSort name body rest = if any (λ entry → primStringEquality name (proj₁ entry)) rest then rest else ((name , body) ∷ rest)
  private
    flattenArray : SortMode → List Segment → ℕ → List JSON → List Statement
  private
    flattenAt : SortMode → List Segment → JSON → List Statement
  private
    flattenObject : SortMode → List Segment → List (String × JSON) → List (String × List Statement)
  flattenArray order revPath i [] = []
  flattenArray order revPath i (v ∷ rest) = flattenAt order (index i ∷ revPath) v ++ flattenArray order revPath (suc i) rest
  flattenAt order revPath (jArray xs) = statement (reverse revPath) (jArray []) ∷ flattenArray order revPath zero xs
  flattenAt order revPath (jObject fields) = statement (reverse revPath) (jObject []) ∷ concat (map proj₂ (flattenObject order revPath fields))
  flattenAt order revPath scalar = statement (reverse revPath) scalar ∷ []
  flattenObject order revPath [] = []
  flattenObject order revPath ((name , v) ∷ rest) = keepMember order name (flattenAt order (key name ∷ revPath) v) (flattenObject order revPath rest)
  flatten : SortMode → JSON → List Statement
  flatten order = flattenAt order []
  private
    editArray : ℕ → (JSON → JSON) → List JSON → List JSON
    editArray zero update [] = update jNull ∷ []
    editArray zero update (v ∷ rest) = update v ∷ rest
    editArray (suc i) update [] = jNull ∷ editArray i update []
    editArray (suc i) update (v ∷ rest) = v ∷ editArray i update rest
  private
    normalizeArray : List JSON → List JSON
  private
    normalizeJSON : JSON → JSON
  private
    normalizeObject : List (String × JSON) → List (String × JSON) → List (String × JSON)
  normalizeArray [] = []
  normalizeArray (v ∷ rest) = normalizeJSON v ∷ normalizeArray rest
  normalizeJSON (jArray xs) = jArray (normalizeArray xs)
  normalizeJSON (jObject fields) = jObject (normalizeObject fields [])
  normalizeJSON scalar = scalar
  normalizeObject [] done = done
  normalizeObject ((name , v) ∷ rest) done = let new = normalizeJSON v in normalizeObject rest (alterSorted name new (λ _ → new) done)
  private
    objectFields : JSON → List (String × JSON)
    objectFields (jObject fields) = fields
    objectFields _ = []
  private
    arrayValues : JSON → List JSON
    arrayValues (jArray xs) = xs
    arrayValues _ = []
  private
    assignAt : List Segment → JSON → JSON → JSON
    assignAt [] (jObject []) (jObject fields) = jObject fields
    assignAt [] (jArray []) (jArray xs) = jArray xs
    assignAt [] new _ = new
    assignAt ((key name) ∷ rest) new old = jObject (alterSorted name (assignAt rest new jNull) (λ v → assignAt rest new v) (objectFields old))
    assignAt ((index i) ∷ rest) new old = jArray (editArray i (λ v → assignAt rest new v) (arrayValues old))
  private
    applyStatement : JSON → Statement → JSON
    applyStatement old (statement path new) = assignAt path (normalizeJSON new) old
  assemble : List Statement → Maybe JSON
  assemble [] = nothing
  assemble (s ∷ rest) = just (foldl applyStatement jNull (s ∷ rest))
  private
    scalarLine : JSON → Maybe String
    scalarLine jNull = just "null"
    scalarLine (jBool true) = just "true"
    scalarLine (jBool false) = just "false"
    scalarLine (jNumber spelling) = just spelling
    scalarLine (jString text) = just (if primStringEquality text "<>&" then "<&>" else text)
    scalarLine (jArray _) = nothing
    scalarLine (jObject _) = nothing
  valueLines : List Statement → List String
  valueLines [] = []
  valueLines ((statement _ v) ∷ rest) with scalarLine v
  valueLines ((statement _ v) ∷ rest) | (just text) = text ∷ valueLines rest
  valueLines ((statement _ v) ∷ rest) | nothing = valueLines rest
  defaultMode : selectMode (modeFlags false false) ≡ gronMode
  defaultMode = refl
  extractMode : selectMode (modeFlags false true) ≡ valuesMode
  extractMode = refl
  reverseMode : (v : Bool) → selectMode (modeFlags true v) ≡ ungronMode
  reverseMode v = refl
  pipeDefault : selectStyle (colorFlags false false stdoutPipe) ≡ plain
  pipeDefault = refl
  ttyDefault : selectStyle (colorFlags false false stdoutTTY) ≡ ansi
  ttyDefault = refl
  monochrome : (sink : StdoutAttachment) → selectStyle (colorFlags false true sink) ≡ plain
  monochrome sink = refl
  forcedColor : (m : Bool) → (sink : StdoutAttachment) → selectStyle (colorFlags true m sink) ≡ ansi
  forcedColor m sink = refl
  identifierExamples : map keyNotation ("$x" ∷ ("_x" ∷ ("a1" ∷ ("é" ∷ ("中" ∷ ("Ⅳ" ∷ ("" ∷ ("01" ∷ ("a b" ∷ ("a.b" ∷ ("😀" ∷ ("℘" ∷ ("١a" ∷ []))))))))))))) ≡ (dotted ∷ (dotted ∷ (dotted ∷ (dotted ∷ (dotted ∷ (dotted ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ [])))))))))))))
  identifierExamples = refl
  reservedExamples : map keyNotation ("class" ∷ ("for" ∷ ("null" ∷ ("super" ∷ ("true" ∷ ("yield" ∷ ("enum" ∷ ("implements" ∷ ("let" ∷ ("undefined" ∷ ("__proto__" ∷ []))))))))))) ≡ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (dotted ∷ (dotted ∷ (dotted ∷ (dotted ∷ (dotted ∷ [])))))))))))
  reservedExamples = refl
  joiningCharacters : map keyNotation (fromList ('a' ∷ (primNatToChar 8204 ∷ [])) ∷ (fromList ('a' ∷ (primNatToChar 8205 ∷ [])) ∷ (fromList ('a' ∷ (primNatToChar 8204 ∷ ('b' ∷ []))) ∷ (fromList ('a' ∷ (primNatToChar 8205 ∷ ('b' ∷ []))) ∷ (fromList (primNatToChar 8204 ∷ ('a' ∷ [])) ∷ (fromList (primNatToChar 8205 ∷ ('a' ∷ [])) ∷ (fromList ('a' ∷ (primNatToChar 8255 ∷ ('b' ∷ []))) ∷ (fromList ('e' ∷ (primNatToChar 769 ∷ [])) ∷ [])))))))) ≡ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (bracketed ∷ (dotted ∷ (dotted ∷ []))))))))
  joiningCharacters = refl
  nullRoot : (order : SortMode) → flatten order jNull ≡ (statement [] jNull ∷ [])
  nullRoot order = refl
  booleanRoot : (order : SortMode) → (b : Bool) → flatten order (jBool b) ≡ (statement [] (jBool b) ∷ [])
  booleanRoot order b = refl
  numberRoot : (order : SortMode) → (spelling : String) → flatten order (jNumber spelling) ≡ (statement [] (jNumber spelling) ∷ [])
  numberRoot order spelling = refl
  stringRoot : (order : SortMode) → (text : String) → flatten order (jString text) ≡ (statement [] (jString text) ∷ [])
  stringRoot order text = refl
  emptyArray : (order : SortMode) → flatten order (jArray []) ≡ (statement [] (jArray []) ∷ [])
  emptyArray order = refl
  emptyObject : (order : SortMode) → flatten order (jObject []) ≡ (statement [] (jObject []) ∷ [])
  emptyObject order = refl
  mixedDocument : flatten sortPaths (jObject (("two words" , jObject []) ∷ (("name" , jString "<&>") ∷ (("items" , jArray (jNumber "1" ∷ (jBool true ∷ (jNull ∷ [])))) ∷ [])))) ≡ (statement [] (jObject []) ∷ (statement (key "items" ∷ []) (jArray []) ∷ (statement (key "items" ∷ (index 0 ∷ [])) (jNumber "1") ∷ (statement (key "items" ∷ (index 1 ∷ [])) (jBool true) ∷ (statement (key "items" ∷ (index 2 ∷ [])) jNull ∷ (statement (key "name" ∷ []) (jString "<&>") ∷ (statement (key "two words" ∷ []) (jObject []) ∷ [])))))))
  mixedDocument = refl
  pathOrder : map Statement.path (flatten sortPaths (jObject (("10" , jNumber "10") ∷ (("2" , jNumber "2") ∷ (("\n" , jNumber "1") ∷ (("	" , jNumber "2") ∷ ((" " , jNumber "3") ∷ (("\"" , jNumber "4") ∷ (("\\" , jNumber "5") ∷ (("!" , jNumber "6") ∷ (("" , jNumber "7") ∷ (("a.b" , jNumber "8") ∷ (("a2" , jNumber "2") ∷ (("a10" , jNumber "10") ∷ (("a" , jObject (("2" , jNumber "2") ∷ (("b" , jNumber "1") ∷ (("!" , jNumber "0") ∷ [])))) ∷ (("items" , jArray (map jNumber ("0" ∷ ("1" ∷ ("2" ∷ ("3" ∷ ("4" ∷ ("5" ∷ ("6" ∷ ("7" ∷ ("8" ∷ ("9" ∷ ("10" ∷ ("11" ∷ [])))))))))))))) ∷ [])))))))))))))))) ≡ ([] ∷ ((key "a" ∷ []) ∷ ((key "a" ∷ (key "b" ∷ [])) ∷ ((key "a" ∷ (key "!" ∷ [])) ∷ ((key "a" ∷ (key "2" ∷ [])) ∷ ((key "a10" ∷ []) ∷ ((key "a2" ∷ []) ∷ ((key "items" ∷ []) ∷ (map (λ i → key "items" ∷ (index i ∷ [])) (upTo 12) ++ ((key " " ∷ []) ∷ ((key "!" ∷ []) ∷ ((key "" ∷ []) ∷ ((key "10" ∷ []) ∷ ((key "2" ∷ []) ∷ ((key "\"" ∷ []) ∷ ((key "\\" ∷ []) ∷ ((key "\n" ∷ []) ∷ ((key "	" ∷ []) ∷ ((key "a.b" ∷ []) ∷ [])))))))))))))))))))
  pathOrder = refl
  joiningPathOrder : map Statement.path (flatten sortPaths (jObject ((fromList ('a' ∷ (primNatToChar 8204 ∷ [])) , jNumber "1") ∷ ((fromList ('a' ∷ (primNatToChar 8205 ∷ [])) , jNumber "2") ∷ ((fromList ('a' ∷ (primNatToChar 8204 ∷ ('b' ∷ []))) , jNumber "3") ∷ ((fromList ('a' ∷ (primNatToChar 8205 ∷ ('b' ∷ []))) , jNumber "4") ∷ ((fromList (primNatToChar 8204 ∷ ('a' ∷ [])) , jNumber "5") ∷ ((fromList (primNatToChar 8205 ∷ ('a' ∷ [])) , jNumber "6") ∷ ((fromList ('e' ∷ (primNatToChar 769 ∷ [])) , jNumber "7") ∷ ((fromList ('a' ∷ (primNatToChar 8255 ∷ ('b' ∷ []))) , jNumber "8") ∷ (("let" , jNumber "9") ∷ (("yield" , jNumber "10") ∷ [])))))))))))) ≡ ([] ∷ ((key (fromList ('a' ∷ (primNatToChar 8255 ∷ ('b' ∷ [])))) ∷ []) ∷ ((key (fromList ('e' ∷ (primNatToChar 769 ∷ []))) ∷ []) ∷ ((key "let" ∷ []) ∷ ((key (fromList ('a' ∷ (primNatToChar 8204 ∷ []))) ∷ []) ∷ ((key (fromList ('a' ∷ (primNatToChar 8204 ∷ ('b' ∷ [])))) ∷ []) ∷ ((key (fromList ('a' ∷ (primNatToChar 8205 ∷ []))) ∷ []) ∷ ((key (fromList ('a' ∷ (primNatToChar 8205 ∷ ('b' ∷ [])))) ∷ []) ∷ ((key "yield" ∷ []) ∷ ((key (fromList (primNatToChar 8204 ∷ ('a' ∷ []))) ∷ []) ∷ ((key (fromList (primNatToChar 8205 ∷ ('a' ∷ []))) ∷ []) ∷ [])))))))))))
  joiningPathOrder = refl
  duplicateMembers : flatten sortPaths (jObject (("a" , jObject (("x" , jNumber "1") ∷ [])) ∷ (("a" , jObject (("y" , jNumber "2") ∷ [])) ∷ (("b" , jNumber "1") ∷ (("b" , jNumber "2") ∷ []))))) ≡ (statement [] (jObject []) ∷ (statement (key "a" ∷ []) (jObject []) ∷ (statement (key "a" ∷ (key "y" ∷ [])) (jNumber "2") ∷ (statement (key "b" ∷ []) (jNumber "2") ∷ []))))
  duplicateMembers = refl
  noStatements : assemble [] ≡ nothing
  noStatements = refl
  sparseArray : assemble (statement (key "z z" ∷ []) (jBool true) ∷ (statement (key "a" ∷ []) (jArray []) ∷ (statement (key "a" ∷ (index 2 ∷ [])) (jString "<>&") ∷ (statement (key "a" ∷ (index 0 ∷ (key "k" ∷ []))) (jNumber "1") ∷ [])))) ≡ just (jObject (("a" , jArray (jObject (("k" , jNumber "1") ∷ []) ∷ (jNull ∷ (jString "<>&" ∷ [])))) ∷ (("z z" , jBool true) ∷ [])))
  sparseArray = refl
  lateEmptyParent : assemble (statement (key "a" ∷ (key "b" ∷ [])) (jNumber "1") ∷ (statement (key "a" ∷ []) (jObject []) ∷ (statement [] (jObject []) ∷ []))) ≡ just (jObject (("a" , jObject (("b" , jNumber "1") ∷ [])) ∷ []))
  lateEmptyParent = refl
  childAfterScalar : assemble (statement (key "a" ∷ []) (jNumber "1") ∷ (statement (key "a" ∷ (key "b" ∷ [])) (jNumber "2") ∷ [])) ≡ just (jObject (("a" , jObject (("b" , jNumber "2") ∷ [])) ∷ []))
  childAfterScalar = refl
  scalarValues : valueLines (statement [] (jObject []) ∷ (statement (key "a" ∷ []) (jArray []) ∷ (statement (key "a" ∷ (index 2 ∷ [])) (jNumber "1e+02") ∷ (statement (key "n" ∷ []) jNull ∷ (statement (key "with space" ∷ []) (jString "<>&") ∷ []))))) ≡ ("1e+02" ∷ ("null" ∷ ("<&>" ∷ [])))
  scalarValues = refl
