{-# OPTIONS --safe #-}
module Context.Tools.NetSandbox where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; fromℕ; toLower)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length; drop)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList; words) renaming (_++_ to _++ˢ_)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.FsSandbox using (eqStr)

digitChar : ℕ → Char
digitChar 0 = '0'
digitChar 1 = '1'
digitChar 2 = '2'
digitChar 3 = '3'
digitChar 4 = '4'
digitChar 5 = '5'
digitChar 6 = '6'
digitChar 7 = '7'
digitChar 8 = '8'
digitChar _ = '9'

decCharsFuel : ℕ → ℕ → List Char → List Char
decCharsFuel zero    _ acc = acc
decCharsFuel (suc f) n acc =
  if n <ᵇ 10 then digitChar n ∷ acc
  else decCharsFuel f (n / 10) (digitChar (n % 10) ∷ acc)

showDec : ℕ → String
showDec n = fromList (decCharsFuel (suc n) n [])

record HttpRoute : Set where
  constructor httpRoute
  field
    routeMethod routePath : String
    routeStatus : ℕ
    routeReason : String
    routeHeaders : List (String × String)
    routeBody : Bytes
open HttpRoute public

record RawStubRule : Set where
  constructor rawStubRule
  field
    matchPrefix replyPayload : Bytes
open RawStubRule public

data NetTopology : Set where
  httpStubMode : List HttpRoute → NetTopology
  tcpStubMode : List RawStubRule → NetTopology
  udpStubMode : List RawStubRule → NetTopology
  daemonProbeMode : String → List String → NetTopology
  httpDelayedStubMode : ℕ → List HttpRoute → NetTopology
  tcpDelayedStubMode : ℕ → List RawStubRule → NetTopology

record NetConfig : Set where
  constructor netConfig
  field
    target : SandboxTarget
    topology : NetTopology
    envVars : List (String × String)
    ownedFiles : List String
open NetConfig public

eqBytes : Bytes → Bytes → Bool
eqBytes [] [] = true
eqBytes (a ∷ as) (b ∷ bs) = (toℕ a ≡ᵇ toℕ b) ∧ eqBytes as bs
eqBytes _ _ = false

eqByteLists : List Bytes → List Bytes → Bool
eqByteLists [] [] = true
eqByteLists (a ∷ as) (b ∷ bs) = eqBytes a b ∧ eqByteLists as bs
eqByteLists _ _ = false

prefixBytes : Bytes → Bytes → Bool
prefixBytes [] _ = true
prefixBytes (_ ∷ _) [] = false
prefixBytes (a ∷ as) (b ∷ bs) = (toℕ a ≡ᵇ toℕ b) ∧ prefixBytes as bs

lower : String → String
lower s = fromList (map toLower (toList s))

hasHeader : String → List (String × String) → Bool
hasHeader key [] = false
hasHeader key ((name , value) ∷ rest) = eqStr (lower key) (lower name) ∨ hasHeader key rest

headerLines : List (String × String) → String
headerLines [] = ""
headerLines ((name , value) ∷ rest) = name ++ˢ ": " ++ˢ value ++ˢ "\r\n" ++ˢ headerLines rest

autoHeader : String → String → List (String × String) → String
autoHeader name value hs = if hasHeader name hs then "" else name ++ˢ ": " ++ˢ value ++ˢ "\r\n"

headerBytes : List (String × String) → Bytes
headerBytes [] = []
headerBytes ((name , value) ∷ rest) =
  bytes name ++ bytes ": " ++ bytes value ++ bytes "\r\n" ++ headerBytes rest

autoHeaderBytes : String → Bytes → List (String × String) → Bytes
autoHeaderBytes name value hs =
  if hasHeader name hs then [] else bytes name ++ bytes ": " ++ value ++ bytes "\r\n"

decBytes : ℕ → Bytes
decBytes n = map (λ c → byte (Data.Char.toℕ c)) (decCharsFuel (suc n) n [])

-- Canonical order: start line, automatic headers, caller headers, blank line.
-- Caller header names suppress automatic headers case-insensitively.
encodeHttpReq : String → String → List (String × String) → Bytes → Bytes
encodeHttpReq method path hs body =
  bytes method ++ bytes " " ++ bytes path ++ bytes " HTTP/1.1\r\n"
  ++ autoHeaderBytes "Host" (bytes "127.0.0.1") hs
  ++ autoHeaderBytes "Connection" (bytes "close") hs
  ++ autoHeaderBytes "Content-Length" (decBytes (length body)) hs
  ++ headerBytes hs ++ bytes "\r\n" ++ body

encodeHttpResp : ℕ → String → List (String × String) → Bytes → Bytes
encodeHttpResp status reason hs body =
  bytes "HTTP/1.1 " ++ decBytes status ++ bytes " " ++ bytes reason ++ bytes "\r\n"
  ++ autoHeaderBytes "Content-Length" (decBytes (length body)) hs
  ++ autoHeaderBytes "Connection" (bytes "close") hs
  ++ headerBytes hs ++ bytes "\r\n" ++ body

record HttpReqView : Set where
  constructor httpReqView
  field
    reqMethod reqTarget : String
    reqBody : Bytes
open HttpReqView public

record HttpRespView : Set where
  constructor httpRespView
  field
    respCode : ℕ
    respBody : Bytes
open HttpRespView public

-- Split only framing bytes; the body is never decoded as text.
splitMarkGo : Bytes → Bytes → Bytes → Maybe (Bytes × Bytes)
splitMarkGo _      _   [] = nothing
splitMarkGo marker acc rest@(b ∷ bs) =
  if prefixBytes marker rest
    then just (reverse acc , drop (length marker) rest)
    else splitMarkGo marker (b ∷ acc) bs

splitMark : Bytes → Bytes → Maybe (Bytes × Bytes)
splitMark marker = splitMarkGo marker []

isAsciiSpaceByte : Byte → Bool
isAsciiSpaceByte b =
  let n = toℕ b
  in (n ≡ᵇ 32) ∨ (n ≡ᵇ 9) ∨ (n ≡ᵇ 10) ∨ (n ≡ᵇ 11) ∨ (n ≡ᵇ 12) ∨ (n ≡ᵇ 13)

flushWordAcc : Bytes → List Bytes
flushWordAcc []       = []
flushWordAcc (x ∷ xs) = reverse (x ∷ xs) ∷ []

wordsBytesGo : Bytes → Bytes → List Bytes
wordsBytesGo acc [] = flushWordAcc acc
wordsBytesGo acc (b ∷ bs) =
  if isAsciiSpaceByte b then
    (flushWordAcc acc ++ wordsBytesGo [] bs)
  else
    wordsBytesGo (b ∷ acc) bs

wordsBytes : Bytes → List Bytes
wordsBytes = wordsBytesGo []

wireText : Bytes → String
wireText bs = fromList (map (λ b → fromℕ (toℕ b)) bs)

httpVersion : String → Bool
httpVersion s = eqStr s "HTTP/1.1" ∨ eqStr s "HTTP/1.0"

httpVersionBytes : Bytes → Bool
httpVersionBytes bs = eqBytes bs (bytes "HTTP/1.1") ∨ eqBytes bs (bytes "HTTP/1.0")

requestLineBytes : List Bytes → Bytes → Maybe HttpReqView
requestLineBytes (methodB ∷ pathB ∷ versionB ∷ []) body =
  if httpVersionBytes versionB
    then just (httpReqView (wireText methodB) (wireText pathB) body)
    else nothing
requestLineBytes _ _ = nothing

requestLine : List String → Bytes → Maybe HttpReqView
requestLine (method ∷ path ∷ version ∷ []) body = if httpVersion version
  then just (httpReqView method path body) else nothing
requestLine _ _ = nothing

parseHttpReq : Bytes → Maybe HttpReqView
parseHttpReq input with splitMark (bytes "\r\n") input | splitMark (bytes "\r\n\r\n") input
... | just (line , _) | just (_ , body) = requestLineBytes (wordsBytes line) body
... | _ | _ = nothing

digitValue : Byte → Maybe ℕ
digitValue b = if (48 ≤ᵇ toℕ b) ∧ (toℕ b <ᵇ 58) then just (toℕ b ∸ 48) else nothing

statusValue : Bytes → Maybe ℕ
statusValue (a ∷ b ∷ c ∷ []) with digitValue a | digitValue b | digitValue c
... | just x | just y | just z = just (100 * x + 10 * y + z)
... | _ | _ | _ = nothing
statusValue _ = nothing

statusView : Maybe ℕ → Bytes → Maybe HttpRespView
statusView nothing body = nothing
statusView (just code) body = just (httpRespView code body)

responseLineBytes : List Bytes → Bytes → Maybe HttpRespView
responseLineBytes (versionB ∷ codeB ∷ _) body =
  if httpVersionBytes versionB then statusView (statusValue codeB) body else nothing
responseLineBytes _ _ = nothing

responseLine : List String → Bytes → Maybe HttpRespView
responseLine (version ∷ code ∷ rest) body = if httpVersion version
  then statusView (statusValue (bytes code)) body else nothing
responseLine _ _ = nothing

parseHttpResp : Bytes → Maybe HttpRespView
parseHttpResp input with splitMark (bytes "\r\n") input | splitMark (bytes "\r\n\r\n") input
... | just (line , _) | just (_ , body) = responseLineBytes (wordsBytes line) body
... | _ | _ = nothing

routeMatch : String → String → Bool
routeMatch expected actual = eqStr expected "*" ∨ eqStr expected actual

matchHttpRoute : List HttpRoute → HttpReqView → Bytes
matchHttpRoute [] req = encodeHttpResp 404 "Not Found" [] []
matchHttpRoute (r ∷ rs) req = if routeMatch (routeMethod r) (reqMethod req) ∧ routeMatch (routePath r) (reqTarget req)
  then encodeHttpResp (routeStatus r) (routeReason r) (routeHeaders r) (routeBody r)
  else matchHttpRoute rs req

matchRawRule : List RawStubRule → Bytes → Bytes
matchRawRule [] input = []
matchRawRule (r ∷ rs) input = if prefixBytes (matchPrefix r) input then replyPayload r else matchRawRule rs input

data NetStep : Set where
  runClient : String → List String → Bytes → ℕ → NetStep
  waitPortReady : ℕ → NetStep
  tcpProbe : Bytes → ℕ → NetStep
  httpProbe : String → String → List (String × String) → Bytes → ℕ → NetStep
  udpProbe : Bytes → ℕ → NetStep
  sleepNetMs : ℕ → NetStep
  drainNet : NetStep

record RawNetObs : Set where
  constructor rawNetObs
  field
    stdoutOut stderrOut wireReply : Bytes
    capturedReqs : List Bytes
    exitStatus : Maybe ℕ
    timedOut : Bool
open RawNetObs public

emptyNetObs : RawNetObs
emptyNetObs = rawNetObs [] [] [] [] nothing false

eqExit : Maybe ℕ → Maybe ℕ → Bool
eqExit nothing nothing = true
eqExit (just a) (just b) = a ≡ᵇ b
eqExit _ _ = false

eqBool : Bool → Bool → Bool
eqBool true true = true
eqBool false false = true
eqBool _ _ = false

eqObs : RawNetObs → RawNetObs → Bool
eqObs a b = eqBytes (stdoutOut a) (stdoutOut b) ∧ eqBytes (stderrOut a) (stderrOut b)
  ∧ eqBytes (wireReply a) (wireReply b) ∧ eqByteLists (capturedReqs a) (capturedReqs b)
  ∧ eqExit (exitStatus a) (exitStatus b) ∧ eqBool (timedOut a) (timedOut b)

eqReqView : HttpReqView → HttpReqView → Bool
eqReqView a b = eqStr (reqMethod a) (reqMethod b)
  ∧ eqStr (reqTarget a) (reqTarget b) ∧ eqBytes (reqBody a) (reqBody b)

eqReqViews : List (Maybe HttpReqView) → List (Maybe HttpReqView) → Bool
eqReqViews [] [] = true
eqReqViews (just a ∷ as) (just b ∷ bs) = eqReqView a b ∧ eqReqViews as bs
eqReqViews (nothing ∷ as) (nothing ∷ bs) = eqReqViews as bs
eqReqViews _ _ = false

httpExchange : List HttpRoute → Maybe HttpReqView → Bytes
httpExchange routes nothing = []
httpExchange routes (just req) = matchHttpRoute routes req

stubReply : NetTopology → Bytes → Bytes
stubReply (httpStubMode routes) input = httpExchange routes (parseHttpReq input)
stubReply (tcpStubMode rules) input = matchRawRule rules input
stubReply (udpStubMode rules) input = matchRawRule rules input
stubReply (daemonProbeMode exe args) input = []
stubReply (httpDelayedStubMode _ routes) input = httpExchange routes (parseHttpReq input)
stubReply (tcpDelayedStubMode _ rules) input = matchRawRule rules input

-- Each supplied payload is one completely framed exchange. Arrival order and
-- all raw request bytes are preserved, including unmatched empty replies.
evalStubExchange : NetTopology → List Bytes → List Bytes × List Bytes
evalStubExchange mode requests = requests , map (stubReply mode) requests

-- A closed daemon model explicitly supplies readiness and a deterministic
-- wire handler. Pending output is consumed once, just like relay pipe drains.
record DaemonModel : Set where
  constructor daemonModel
  field
    daemonReady : Bool
    daemonHandler : Bytes → Bytes
    daemonOut daemonErr : Bytes
    daemonExit : Maybe ℕ
open DaemonModel public

modelWire : DaemonModel → NetStep → Bytes
modelWire model (tcpProbe input ms) = daemonHandler model input
modelWire model (httpProbe method path hs body ms) = daemonHandler model (encodeHttpReq method path hs body)
modelWire model (udpProbe input ms) = daemonHandler model input
modelWire model _ = []

modelTimeout : DaemonModel → NetStep → Bool
modelTimeout model (waitPortReady ms) = if daemonReady model then false else true
modelTimeout model _ = false

stepDaemonModel : DaemonModel → NetStep → DaemonModel × RawNetObs
stepDaemonModel model step = daemonModel (daemonReady model) (daemonHandler model) [] [] nothing
  , rawNetObs (daemonOut model) (daemonErr model) (modelWire model step) [] (daemonExit model) (modelTimeout model step)

traceDaemonModel : DaemonModel → List NetStep → List RawNetObs
traceDaemonModel model [] = []
traceDaemonModel model (step ∷ steps) with stepDaemonModel model step
... | next , obs = obs ∷ traceDaemonModel next steps
