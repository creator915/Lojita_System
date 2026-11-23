import LojitaCtx.FsSandbox

namespace LojitaCtx.NetSandbox

open LojitaCtx.Terminal

def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

def decCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | Nat.succ f, n, acc =>
    if n < 10 then digitChar n :: acc else decCharsFuel f (n / 10) (digitChar (n % 10) :: acc)
termination_by structural f _ _ => f

def showDec (n : Nat) : String :=
  String.ofList (decCharsFuel (Nat.succ n) n [])

structure HttpRoute : Type where httpRoute ::
  routeMethod : String
  routePath : String
  routeStatus : Nat
  routeReason : String
  routeHeaders : List (String × String)
  routeBody : Bytes

structure RawStubRule : Type where
  rawStubRule ::
  matchPrefix  : Bytes
  replyPayload : Bytes

inductive NetTopology : Type where
  | httpStubMode        : List HttpRoute → NetTopology
  | tcpStubMode         : List RawStubRule → NetTopology
  | udpStubMode         : List RawStubRule → NetTopology
  | daemonProbeMode     : String → List String → NetTopology
  | httpDelayedStubMode : Nat → List HttpRoute → NetTopology
  | tcpDelayedStubMode  : Nat → List RawStubRule → NetTopology

structure NetConfig : Type where netConfig ::
  target : SandboxTarget
  topology : NetTopology
  envVars : List (String × String)
  ownedFiles : List String

def eqBytes : Bytes → Bytes → Bool :=
  FsSandbox.eqBytes

def eqByteLists : List Bytes → List Bytes → Bool
  | [], [] => true
  | a :: as, b :: bs => eqBytes a b && eqByteLists as bs
  | _, _ => false
termination_by structural as _ => as

def prefixBytes : Bytes → Bytes → Bool :=
  FsSandbox.prefixBytes

def lower (s : String) : String :=
  String.ofList (List.map Char.toLower (String.toList s))

def hasHeader (key : String) : List (String × String) → Bool
  | [] => false
  | nv :: rest => FsSandbox.eqStr (lower key) (lower nv.1) || hasHeader key rest
termination_by structural hs => hs

def headerLines : List (String × String) → String
  | [] => ""
  | nv :: rest => nv.1 ++ (": " ++ (nv.2 ++ ("\r\n" ++ headerLines rest)))
termination_by structural hs => hs

def autoHeader (name value : String) (hs : List (String × String)) : String :=
  if hasHeader name hs then "" else name ++ (": " ++ (value ++ "\r\n"))

def headerBytes : List (String × String) → Bytes
  | [] => []
  | nv :: rest => bytes nv.1 ++ (bytes ": " ++ (bytes nv.2 ++ (bytes "\r\n" ++ headerBytes rest)))
termination_by structural hs => hs

def autoHeaderBytes (name : String) (value : Bytes) (hs : List (String × String)) : Bytes :=
  if hasHeader name hs then [] else bytes name ++ (bytes ": " ++ (value ++ bytes "\r\n"))

def decBytes (n : Nat) : Bytes :=
  List.map (fun c => byte (Char.toNat c)) (decCharsFuel (Nat.succ n) n [])

def encodeHttpReq (method path : String) (hs : List (String × String)) (body : Bytes) : Bytes :=
  bytes method ++
    (bytes " " ++
      (bytes path ++
        (bytes " HTTP/1.1\r\n" ++
          (autoHeaderBytes "Host" (bytes "127.0.0.1") hs ++
            (autoHeaderBytes "Connection" (bytes "close") hs ++
              (autoHeaderBytes "Content-Length" (decBytes (List.length body)) hs ++
                (headerBytes hs ++ (bytes "\r\n" ++ body))))))))

def encodeHttpResp (status : Nat) (reason : String) (hs : List (String × String)) (body : Bytes) :
    Bytes :=
  bytes "HTTP/1.1 " ++
    (decBytes status ++
      (bytes " " ++
        (bytes reason ++
          (bytes "\r\n" ++
            (autoHeaderBytes "Content-Length" (decBytes (List.length body)) hs ++
              (autoHeaderBytes "Connection" (bytes "close") hs ++
                (headerBytes hs ++ (bytes "\r\n" ++ body))))))))

structure HttpReqView : Type where
  httpReqView ::
  reqMethod : String
  reqTarget : String
  reqBody   : Bytes

structure HttpRespView : Type where
  httpRespView ::
  respCode : Nat
  respBody : Bytes

def splitMarkGo (marker : Bytes) : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => .none
  | acc, b :: bs =>
    let rest := b :: bs
    if prefixBytes marker rest then
      .some (Prod.mk (List.reverse acc) (List.drop (List.length marker) rest))
    else splitMarkGo marker (b :: acc) bs
termination_by structural _ rest => rest

def splitMark (marker : Bytes) : Bytes → Option (Bytes × Bytes) :=
  splitMarkGo marker []

def isAsciiSpaceByte (b : Byte) : Bool :=
  let n := UInt8.toNat b
  n == 32 || (n == 9 || (n == 10 || (n == 11 || (n == 12 || n == 13))))

def flushWordAcc : Bytes → List Bytes
  | []      => []
  | x :: xs => [List.reverse (x :: xs)]

def wordsBytesGo : Bytes → Bytes → List Bytes
  | acc, [] => flushWordAcc acc
  | acc, b :: bs =>
    if isAsciiSpaceByte b then flushWordAcc acc ++ wordsBytesGo [] bs
    else wordsBytesGo (b :: acc) bs
termination_by structural _ bs => bs

def wordsBytes : Bytes → List Bytes :=
  wordsBytesGo []

def wireText (bs : Bytes) : String :=
  String.ofList (List.map (fun b => Char.ofNat (UInt8.toNat b)) bs)

def httpVersion (s : String) : Bool :=
  FsSandbox.eqStr s "HTTP/1.1" || FsSandbox.eqStr s "HTTP/1.0"

def httpVersionBytes (bs : Bytes) : Bool :=
  eqBytes bs (bytes "HTTP/1.1") || eqBytes bs (bytes "HTTP/1.0")

def requestLineBytes : List Bytes → Bytes → Option HttpReqView
  | [methodB, pathB, versionB], body =>
      (if (httpVersionBytes versionB) then (.some (HttpReqView.httpReqView (wireText methodB) (wireText pathB) body)) else .none)
  | _, _ => .none

def requestLine : List String → Bytes → Option HttpReqView
  | [method, path, version], body =>
      (if (httpVersion version) then (.some (HttpReqView.httpReqView method path body)) else .none)
  | _, _ => .none

def parseHttpReq (input : Bytes) : Option HttpReqView :=
  match splitMark (bytes "\r\n") input, splitMark (bytes "\r\n\r\n") input with
  | .some lineRem, .some hdrBody => requestLineBytes (wordsBytes lineRem.1) hdrBody.2
  | _, _ => .none

def digitValue (b : Byte) : Option Nat :=
  if 48 ≤ UInt8.toNat b && UInt8.toNat b < 58 then .some (UInt8.toNat b - 48) else .none

def statusValue : Bytes → Option Nat
  | [a, b, c] =>
    match digitValue a, digitValue b, digitValue c with
    | .some x, .some y, .some z => .some (100 * x + (10 * y + z))
    | _, _, _ => .none
  | _ => .none

def statusView : Option Nat → Bytes → Option HttpRespView
  | .none,   _    => .none
  | .some code, body => .some (HttpRespView.httpRespView code body)

def responseLineBytes : List Bytes → Bytes → Option HttpRespView
  | versionB :: codeB :: _, body =>
      (if (httpVersionBytes versionB) then (statusView (statusValue codeB) body) else .none)
  | _, _ => .none

def responseLine : List String → Bytes → Option HttpRespView
  | version :: code :: _, body =>
      (if (httpVersion version) then (statusView (statusValue (bytes code)) body) else .none)
  | _, _ => .none

def parseHttpResp (input : Bytes) : Option HttpRespView :=
  match splitMark (bytes "\r\n") input, splitMark (bytes "\r\n\r\n") input with
  | .some lineRem, .some hdrBody => responseLineBytes (wordsBytes lineRem.1) hdrBody.2
  | _, _ => .none

def routeMatch (expected actual : String) : Bool :=
  FsSandbox.eqStr expected "*" || FsSandbox.eqStr expected actual

def matchHttpRoute : List HttpRoute → HttpReqView → Bytes
  | [], _ => encodeHttpResp 404 "Not Found" [] []
  | r :: rs, req =>
    if routeMatch r.routeMethod req.reqMethod && routeMatch r.routePath req.reqTarget then
      encodeHttpResp r.routeStatus r.routeReason r.routeHeaders r.routeBody
    else matchHttpRoute rs req
termination_by structural rs _ => rs

def matchRawRule : List RawStubRule → Bytes → Bytes
  | [], _          => []
  | r :: rs, input => (if (prefixBytes r.matchPrefix input) then r.replyPayload else (matchRawRule rs input))
termination_by structural rs _ => rs

inductive NetStep : Type where
  | runClient : String → List String → Bytes → Nat → NetStep
  | waitPortReady : Nat → NetStep
  | tcpProbe : Bytes → Nat → NetStep
  | httpProbe : String → String → List (String × String) → Bytes → Nat → NetStep
  | udpProbe : Bytes → Nat → NetStep
  | sleepNetMs : Nat → NetStep
  | drainNet : NetStep

structure RawNetObs : Type where
  rawNetObs ::
  stdoutOut    : Bytes
  stderrOut    : Bytes
  wireReply    : Bytes
  capturedReqs : List Bytes
  exitStatus   : Option Nat
  timedOut     : Bool

def emptyNetObs : RawNetObs :=
  RawNetObs.rawNetObs [] [] [] [] .none false

def eqExit : Option Nat → Option Nat → Bool := FsSandbox.eqExit
def eqBool : Bool → Bool → Bool := FsSandbox.eqBool

def eqObs (a b : RawNetObs) : Bool :=
  eqBytes a.stdoutOut b.stdoutOut &&
    (eqBytes a.stderrOut b.stderrOut &&
      (eqBytes a.wireReply b.wireReply &&
        (eqByteLists a.capturedReqs b.capturedReqs &&
          (eqExit a.exitStatus b.exitStatus && eqBool a.timedOut b.timedOut))))

def eqReqView (a b : HttpReqView) : Bool :=
  FsSandbox.eqStr a.reqMethod b.reqMethod &&
    (FsSandbox.eqStr a.reqTarget b.reqTarget && eqBytes a.reqBody b.reqBody)

def eqReqViews : List (Option HttpReqView) → List (Option HttpReqView) → Bool
  | [], [] => true
  | .some a :: as, .some b :: bs => eqReqView a b && eqReqViews as bs
  | .none :: as, .none :: bs => eqReqViews as bs
  | _, _ => false
termination_by structural as _ => as

def httpExchange (routes : List HttpRoute) : Option HttpReqView → Bytes
  | .none  => []
  | .some req => matchHttpRoute routes req

def stubReply : NetTopology → Bytes → Bytes
  | .httpStubMode routes,          input => httpExchange routes (parseHttpReq input)
  | .tcpStubMode rules,            input => matchRawRule rules input
  | .udpStubMode rules,            input => matchRawRule rules input
  | .daemonProbeMode _ _,          _     => []
  | .httpDelayedStubMode _ routes, input => httpExchange routes (parseHttpReq input)
  | .tcpDelayedStubMode _ rules,   input => matchRawRule rules input

def evalStubExchange (mode : NetTopology) (requests : List Bytes) : List Bytes × List Bytes :=
  Prod.mk requests (List.map (stubReply mode) requests)

structure DaemonModel : Type where
  daemonModel ::
  daemonReady   : Bool
  daemonHandler : Bytes → Bytes
  daemonOut     : Bytes
  daemonErr     : Bytes
  daemonExit    : Option Nat

def modelWire (model : DaemonModel) : NetStep → Bytes
  | .tcpProbe input _               => model.daemonHandler input
  | .httpProbe method path hs body _ => model.daemonHandler (encodeHttpReq method path hs body)
  | .udpProbe input _               => model.daemonHandler input
  | _                               => []

def modelTimeout (model : DaemonModel) : NetStep → Bool
  | .waitPortReady _ => (if model.daemonReady then false else true)
  | _                => false

def stepDaemonModel (model : DaemonModel) (st : NetStep) : (DaemonModel × RawNetObs) :=
  Prod.mk
    (DaemonModel.daemonModel model.daemonReady model.daemonHandler [] [] .none)
    (RawNetObs.rawNetObs model.daemonOut model.daemonErr (modelWire model st) [] model.daemonExit (modelTimeout model st))

def traceDaemonModel (model : DaemonModel) : List NetStep → List RawNetObs
  | []        => []
  | st :: sts =>
      let r := stepDaemonModel model st
      r.2 :: traceDaemonModel r.1 sts
termination_by structural sts => sts

end LojitaCtx.NetSandbox
