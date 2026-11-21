{-# OPTIONS --safe #-}
module Test.Tools.NetConformance where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (Bytes; byte; bytes)
open import Context.Tools.NetSandbox

binaryBody : Bytes
binaryBody = byte 0 ∷ byte 255 ∷ byte 13 ∷ byte 10 ∷ byte 65 ∷ []

getWire : Bytes
getWire = encodeHttpReq "GET" "/items?page=1" [] []

postWire : Bytes
postWire = encodeHttpReq "POST" "/submit" (("Content-Type" , "application/octet-stream") ∷ []) binaryBody

get-roundtrip : parseHttpReq getWire ≡ just (httpReqView "GET" "/items?page=1" [])
get-roundtrip = refl

get-binary-roundtrip : parseHttpReq (encodeHttpReq "GET" "/items?page=1" [] binaryBody) ≡
  just (httpReqView "GET" "/items?page=1" binaryBody)
get-binary-roundtrip = refl

post-binary-roundtrip : parseHttpReq postWire ≡ just (httpReqView "POST" "/submit" binaryBody)
post-binary-roundtrip = refl

ok-roundtrip : parseHttpResp (encodeHttpResp 200 "OK" [] binaryBody) ≡ just (httpRespView 200 binaryBody)
ok-roundtrip = refl

not-found-roundtrip : parseHttpResp (encodeHttpResp 404 "Not Found" [] []) ≡ just (httpRespView 404 [])
not-found-roundtrip = refl

-- This fixes the exact canonical wire format, including zero-length bodies.
canonical-get : encodeHttpReq "GET" "/" [] [] ≡
  bytes "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"
canonical-get = refl

canonical-response : encodeHttpResp 200 "OK" [] [] ≡
  bytes "HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
canonical-response = refl

header-override : encodeHttpReq "GET" "/" (("hOsT" , "example") ∷ ("connection" , "keep-alive")
  ∷ ("content-length" , "0") ∷ []) [] ≡
  bytes "GET / HTTP/1.1\r\nhOsT: example\r\nconnection: keep-alive\r\ncontent-length: 0\r\n\r\n"
header-override = refl

incomplete-request : parseHttpReq (bytes "GET / HTTP/1.1\r\nHost: local\r\n") ≡ nothing
incomplete-request = refl

invalid-status : parseHttpResp (bytes "HTTP/1.1 2x0 Invalid\r\n\r\n") ≡ nothing
invalid-status = refl

routes : List HttpRoute
routes = httpRoute "GET" "/items" 200 "OK" (("Content-Type" , "application/json") ∷ []) (bytes "[1,2]")
  ∷ httpRoute "POST" "/submit" 201 "Created" [] binaryBody ∷ []

priority-routes : List HttpRoute
priority-routes = httpRoute "*" "/items" 202 "Accepted" [] (bytes "first")
  ∷ httpRoute "GET" "/items" 200 "OK" [] (bytes "second") ∷ []

route-priority : matchHttpRoute priority-routes (httpReqView "GET" "/items" []) ≡
  encodeHttpResp 202 "Accepted" [] (bytes "first")
route-priority = refl

method-wildcard : matchHttpRoute priority-routes (httpReqView "PATCH" "/items" binaryBody) ≡
  encodeHttpResp 202 "Accepted" [] (bytes "first")
method-wildcard = refl

path-wildcard : matchHttpRoute (httpRoute "GET" "*" 200 "OK" [] binaryBody ∷ [])
  (httpReqView "GET" "/anything?query=1" []) ≡ encodeHttpResp 200 "OK" [] binaryBody
path-wildcard = refl

query-exact : matchHttpRoute (httpRoute "GET" "/items?page=1" 200 "OK" [] binaryBody ∷ [])
  (httpReqView "GET" "/items?page=1" []) ≡ encodeHttpResp 200 "OK" [] binaryBody
query-exact = refl

query-not-stripped : matchHttpRoute routes (httpReqView "GET" "/items?page=1" []) ≡
  encodeHttpResp 404 "Not Found" [] []
query-not-stripped = refl

fallback-404 : matchHttpRoute routes (httpReqView "GET" "/missing" []) ≡ encodeHttpResp 404 "Not Found" [] []
fallback-404 = refl

httpRequests : List Bytes
httpRequests = encodeHttpReq "GET" "/items" [] [] ∷ postWire ∷ encodeHttpReq "GET" "/missing" [] [] ∷ []

http-trace : evalStubExchange (httpStubMode routes) httpRequests ≡
  (httpRequests , encodeHttpResp 200 "OK" (("Content-Type" , "application/json") ∷ []) (bytes "[1,2]")
    ∷ encodeHttpResp 201 "Created" [] binaryBody ∷ encodeHttpResp 404 "Not Found" [] [] ∷ [])
http-trace = refl

rawRules : List RawStubRule
rawRules = rawStubRule (byte 0 ∷ byte 255 ∷ []) binaryBody
  ∷ rawStubRule (bytes "ping") (bytes "pong")
  ∷ rawStubRule [] (bytes "fallback") ∷ []

rawRequests : List Bytes
rawRequests = binaryBody ∷ bytes "ping more" ∷ bytes "unknown" ∷ []

tcp-trace : evalStubExchange (tcpStubMode rawRules) rawRequests ≡
  (rawRequests , binaryBody ∷ bytes "pong" ∷ bytes "fallback" ∷ [])
tcp-trace = refl

udp-trace : evalStubExchange (udpStubMode rawRules) rawRequests ≡
  (rawRequests , binaryBody ∷ bytes "pong" ∷ bytes "fallback" ∷ [])
udp-trace = refl

raw-no-match : matchRawRule (rawStubRule (bytes "prefix") binaryBody ∷ []) (bytes "other") ≡ []
raw-no-match = refl

raw-priority : matchRawRule (rawStubRule [] binaryBody ∷ rawStubRule (bytes "ping") [] ∷ [])
  (bytes "ping") ≡ binaryBody
raw-priority = refl

-- The daemon is modeled as a pure HTTP echo handler; drains consume output.
echoHandler : Bytes → Bytes
echoHandler input with parseHttpReq input
... | nothing = []
... | just req = encodeHttpResp 200 "OK" [] (reqBody req)

daemon-trace : traceDaemonModel (daemonModel true echoHandler (bytes "ready\n") [] nothing)
  (waitPortReady 5000 ∷ httpProbe "POST" "/echo" [] binaryBody 5000 ∷ drainNet ∷ []) ≡
  (rawNetObs (bytes "ready\n") [] [] [] nothing false
  ∷ rawNetObs [] [] (encodeHttpResp 200 "OK" [] binaryBody) [] nothing false
  ∷ emptyNetObs ∷ [])
daemon-trace = refl

exit-drain : traceDaemonModel (daemonModel false echoHandler [] [] (just 7))
  (drainNet ∷ drainNet ∷ []) ≡
  (rawNetObs [] [] [] [] (just 7) false ∷ emptyNetObs ∷ [])
exit-drain = refl
