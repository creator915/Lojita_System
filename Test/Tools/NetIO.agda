{-# OPTIONS --guardedness #-}
module Test.Tools.NetIO where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concat)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; File; Chan; Srv; Prog; done; openAs; call; stop;
  _>>=_; _>>_; ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (evalIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure)
open import OwnershipIO.Tools.NetFFI using (localOnly)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.NetSandbox
open import Code.Tools.NetTool
open import Code.Driver using (Registry; Pick; SubT; select; all-nil; all-cons)
open import Test.Tools.NetConformance using (echoHandler)

Home Live : NetConfig → St
Home cfg = Dir (("slot" , Dir (NetOwnedCtx cfg)) ∷ [])
Live cfg = Dir (("slot" , Chan (Srv NetStep RawNetObs (Dir (NetOwnedCtx cfg)))) ∷ [])

calls : (cfg : NetConfig) → List NetStep → Prog (netSpec ∷ []) (Live cfg) (Live cfg) (List RawNetObs)
calls cfg [] = done []
calls cfg (q ∷ qs) = call "slot" q >>= λ o → calls cfg qs >>= λ os → done (o ∷ os)

session : (cfg : NetConfig) → List NetStep → Prog (netSpec ∷ []) (Home cfg) (Home cfg) (List RawNetObs)
session cfg qs = openAs "slot" "netbox" cfg >> calls cfg qs >>= λ observations →
  stop "slot" >> done observations

registry : String → Registry (netSpec ∷ [])
registry cwd = netTool (cwd ++ˢ "/tmp/ext-tools-build/net-relay") (cwd ++ˢ "/tmp/net-sandboxes") ∷ []

report : String → Bool → IO.IO Bool
report label b = F.putStrLn ((if b then "PASS " else "FAIL ") ++ˢ label) IO.>>= λ _ → IO.return b

env : List (String × String)
env = ("DECLARED" , "visible") ∷ ("LC_ALL" , "C.UTF-8") ∷
  ("NET_ADDR" , "{{ADDR}}") ∷ ("NET_URL" , "{{URL}}") ∷ ("NET_PORT" , "{{PORT}}") ∷ []

python : String → List String → Bytes → ℕ → NetStep
python source args input timeout = runClient "/usr/bin/python3"
  ("-I" ∷ "-S" ∷ "-c" ∷ source ∷ args) input timeout

binary : Bytes
binary = byte 0 ∷ byte 255 ∷ byte 13 ∷ byte 10 ∷ byte 128 ∷ []

routes : List HttpRoute
routes = httpRoute "GET" "/items" 200 "OK" (("Content-Type" , "application/json") ∷ []) (bytes "[1,2]") ∷
  httpRoute "POST" "/submit" 201 "Created" [] binary ∷ []

requests : List Bytes
requests = encodeHttpReq "GET" "/items" [] [] ∷ encodeHttpReq "POST" "/submit" [] binary ∷
  encodeHttpReq "GET" "/missing" [] [] ∷ []

-- A real socket client writes each request in pieces and reads to EOF. The
-- expected response bytes and captured request bytes come from the pure model.
httpClient : String
httpClient = "import socket,sys; out=b''\n"
  ++ˢ "for q in sys.argv[2:]:\n"
  ++ˢ " s=socket.create_connection(('127.0.0.1',int(sys.argv[1]))); b=bytes.fromhex(q); s.sendall(b[:7]); s.sendall(b[7:]); r=b''\n"
  ++ˢ " while True:\n  x=s.recv(65536)\n  if not x: break\n  r+=x\n"
  ++ˢ " s.close(); out+=r\n"
  ++ˢ "open('result.bin','wb').write(out); sys.stdout.buffer.write(out)"

singleExchange : NetTopology → List Bytes → List RawNetObs → Bool
singleExchange mode inputs (o ∷ []) = eqExit (exitStatus o) (just 0) ∧ not (timedOut o)
  ∧ eqBytes (stderrOut o) [] ∧ eqBytes (wireReply o) []
  ∧ eqBytes (stdoutOut o) (concat (proj₂ (evalStubExchange mode inputs)))
  ∧ eqByteLists (capturedReqs o) (proj₁ (evalStubExchange mode inputs))
singleExchange _ _ _ = false

httpCaptured : List RawNetObs → Bool
httpCaptured (o ∷ []) = eqReqViews (map parseHttpReq (capturedReqs o)) (map parseHttpReq requests)
httpCaptured _ = false

httpConformance : String → SandboxTarget → IO.IO Bool
httpConformance cwd destination = evalIO (select (netSpec ∷ []) (registry cwd))
  (session cfg (python httpClient ("{{PORT}}" ∷ map hexBytes requests) [] 5000 ∷ []))
  (([] , tt) , tt) IO.>>= λ result → report "HTTP sequential GET/POST/404: exact pure wires, parsed captures, owned bytes"
    (singleExchange mode requests (proj₂ result) ∧ httpCaptured (proj₂ result)
      ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) (concat (proj₂ (evalStubExchange mode requests))))
  where
    mode = httpStubMode routes
    cfg = netConfig destination mode env ("result.bin" ∷ [])

packets : List Bytes
packets = (byte 0 ∷ byte 255 ∷ byte 1 ∷ byte 0 ∷ []) ∷ (byte 128 ∷ byte 0 ∷ byte 13 ∷ byte 10 ∷ []) ∷ []

rules : List RawStubRule
rules = rawStubRule (byte 0 ∷ byte 255 ∷ []) binary ∷ rawStubRule [] (bytes "fallback\0") ∷ []

udpClient : String
udpClient = "import socket,sys; s=socket.socket(socket.AF_INET,socket.SOCK_DGRAM); s.settimeout(2); out=b''\n"
  ++ˢ "for q in sys.argv[2:]:\n s.sendto(bytes.fromhex(q),('127.0.0.1',int(sys.argv[1]))); out+=s.recv(65536)\n"
  ++ˢ "s.close(); sys.stdout.buffer.write(out)"

tcpClient : String
tcpClient = "import socket,sys; out=b''\n"
  ++ˢ "for q in sys.argv[2:]:\n s=socket.create_connection(('127.0.0.1',int(sys.argv[1]))); s.sendall(bytes.fromhex(q)); s.shutdown(socket.SHUT_WR)\n"
  ++ˢ " while True:\n  b=s.recv(65536)\n  if not b: break\n  out+=b\n s.close()\n"
  ++ˢ "sys.stdout.buffer.write(out)"

rawConformance : String → SandboxTarget → NetTopology → String → String → IO.IO Bool
rawConformance cwd destination mode client label = evalIO (select (netSpec ∷ []) (registry cwd))
  (session (netConfig destination mode env []) (python client ("{{PORT}}" ∷ map hexBytes packets) [] 5000 ∷ []))
  (tt , tt) IO.>>= λ result → report label (singleExchange mode packets (proj₂ result))

-- Readiness connections carry no request. The single actual HTTP exchange is
-- logged verbatim into the owned file before the response is sent.
httpDaemon : String
httpDaemon = "import os,socket,sys; s=socket.socket(); s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1); "
  ++ˢ "s.bind(('127.0.0.1',int(sys.argv[1]))); s.listen(16)\n"
  ++ˢ "assert os.environ['NET_PORT']==sys.argv[1]; assert 'HOST_SECRET_LEAK' not in os.environ\n"
  ++ˢ "while True:\n c,a=s.accept(); b=b''\n while b'\\r\\n\\r\\n' not in b:\n  x=c.recv(65536)\n  if not x: break\n  b+=x\n"
  ++ˢ " if not b: c.close(); continue\n"
  ++ˢ " h,body=b.split(b'\\r\\n\\r\\n',1); n=int([x.split(b':',1)[1] for x in h.split(b'\\r\\n')[1:] if x.lower().startswith(b'content-length:')][0])\n"
  ++ˢ " while len(body)<n:\n  x=c.recv(65536)\n  if not x: raise RuntimeError('premature EOF')\n  body+=x; b+=x\n"
  ++ˢ " with open('daemon.log','ab') as f: f.write(b); f.flush()\n"
  ++ˢ " c.sendall(bytes.fromhex(sys.argv[2])); c.close()\n"

daemonReply : Bytes
daemonReply = encodeHttpResp 200 "OK" [] binary

daemonSteps : List NetStep
daemonSteps = waitPortReady 5000 ∷ httpProbe "POST" "/echo" [] binary 5000 ∷ sleepNetMs 20 ∷ drainNet ∷ []

eqNetTrace : List RawNetObs → List RawNetObs → Bool
eqNetTrace [] [] = true
eqNetTrace (a ∷ as) (b ∷ bs) = eqObs a b ∧ eqNetTrace as bs
eqNetTrace _ _ = false

daemonObservations : List RawNetObs → Bool
daemonObservations observations = eqNetTrace observations
  (traceDaemonModel (daemonModel true echoHandler [] [] nothing) daemonSteps)

daemonConformance : String → SandboxTarget → IO.IO Bool
daemonConformance cwd destination = evalIO (select (netSpec ∷ []) (registry cwd))
  (session cfg daemonSteps)
  (([] , tt) , tt) IO.>>= λ result → report "HTTP daemon readiness/probe/drain/stop returns owned request log via Registry/select"
    (daemonObservations (proj₂ result) ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) (encodeHttpReq "POST" "/echo" [] binary))
  where
    mode = daemonProbeMode "/usr/bin/python3" ("-I" ∷ "-S" ∷ "-c" ∷ httpDaemon ∷ "{{PORT}}" ∷ hexBytes daemonReply ∷ [])
    cfg = netConfig destination mode env ("daemon.log" ∷ [])

cleanClient : String
cleanClient = "import os,socket,sys; p=sys.argv[1]; "
  ++ˢ "assert set(os.environ)=={'DECLARED','LC_ALL','NET_PORT','NET_ADDR','NET_URL'}; "
  ++ˢ "assert os.environ['DECLARED']=='visible'; assert os.environ['NET_PORT']==p; "
  ++ˢ "assert os.environ['NET_ADDR']=='127.0.0.1:'+p; assert os.environ['NET_URL']=='http://127.0.0.1:'+p; "
  ++ˢ "s=socket.create_connection(('127.0.0.1',int(p))); s.sendall(b'ping'); s.shutdown(socket.SHUT_WR); "
  ++ˢ "sys.stdout.buffer.write(s.recv(4096)); s.close()"

timeoutObservations : List RawNetObs → Bool
timeoutObservations (hung ∷ next ∷ []) = timedOut hung ∧ eqExit (exitStatus hung) (just 124)
  ∧ eqExit (exitStatus next) (just 0) ∧ not (timedOut next) ∧ eqBytes (stdoutOut next) (bytes "pong")
  ∧ eqBytes (stderrOut next) [] ∧ eqByteLists (capturedReqs next) (bytes "ping" ∷ [])
timeoutObservations _ = false

timeoutConformance : String → SandboxTarget → IO.IO Bool
timeoutConformance cwd destination = evalIO (select (netSpec ∷ []) (registry cwd))
  (session cfg (python "import time; time.sleep(60)" [] [] 200 ∷ python cleanClient ("{{PORT}}" ∷ []) [] 5000 ∷ []))
  (tt , tt) IO.>>= λ result → report "hung client killed; persistent stub reusable; exact clean substituted environment"
    (timeoutObservations (proj₂ result))
  where
    cfg = netConfig destination (tcpStubMode (rawStubRule [] (bytes "pong") ∷ [])) env []

suite : String → SandboxTarget → IO.IO Bool
suite cwd destination = httpConformance cwd destination IO.>>= λ a →
  rawConformance cwd destination (udpStubMode rules) udpClient "UDP binary packets match pure prefix model" IO.>>= λ b →
  rawConformance cwd destination (tcpStubMode rules) tcpClient "TCP binary requests match pure prefix model" IO.>>= λ c →
  daemonConformance cwd destination IO.>>= λ d →
  timeoutConformance cwd destination IO.>>= λ e → IO.return (a ∧ b ∧ c ∧ d ∧ e)

dockerSuite : String → Bool → IO.IO Bool
dockerSuite cwd true = F.putStrLn "Docker omitted by explicit --local-only" IO.>>= λ _ → IO.return true
dockerSuite cwd false = F.putStrLn "Docker loopback network conformance" IO.>>= λ _ →
  suite cwd (dockerSandbox "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6")

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → localOnly IO.>>= λ onlyLocal →
  F.putStrLn "Local loopback network conformance" IO.>>= λ _ → suite cwd localSandbox IO.>>= λ localOK →
  dockerSuite cwd onlyLocal IO.>>= λ dockerOK →
  if localOK ∧ dockerOK then F.putStrLn "ALL NETWORK TESTS PASS" else exitFailure
