import Lojita.Ownership.Tools.Relay

set_option genCtorIdx false

namespace Lojita.Ownership.Tools.Web
open LojitaCtx.Terminal

structure WebConfig where
  target : SandboxTarget
  width : Nat
  height : Nat
  ownedFiles : List String

inductive WebStep where
  | flush (wire : String)
  | pixel (x y : Nat)
  | resize (width height : Nat)
  | exportPPM (path : String)

inductive RawWebObs where
  | ack
  | frame (count digest : Nat)
  | pixelObs (present : Bool) (r g b : UInt8)
deriving BEq, Repr

def webSpec := OwnedSpec "webcanvas" WebConfig Bytes WebStep RawWebObs WebConfig.ownedFiles

private def channel (s : String) : IO UInt8 := do
  let n ← natural s
  requireWire (n ≤ 255) "invalid web color"
  return n.toUInt8

def request (p : Pipe) (line : String) : IO RawWebObs := do
  match ← exchange p line with
  | ["OK"] => return .ack
  | ["FRAME", n, d] => return .frame (← natural n) (← natural d)
  | ["PIXEL", present, r, g, b] => return .pixelObs (← flag present) (← channel r) (← channel g) (← channel b)
  | _ => throw (IO.userError "invalid canvas reply")

def webTool (bin scratch : System.FilePath) : HandlerIO webSpec := fun cfg owned =>
  openBytes bin scratch cfg.target cfg.ownedFiles owned
    (#[toString cfg.width, toString cfg.height] ++ cfg.ownedFiles.toArray) (fun _ => pure ())
    (fun p q => do
      match q with
      | .flush wire => request p ("FLUSH " ++ hexText wire)
      | .pixel x y => request p s!"PIXEL {x} {y}"
      | .resize w h => request p s!"RESIZE {w} {h}"
      | .exportPPM path =>
        requireWire (cfg.ownedFiles.contains path) "export requires an owned file"
        request p ("EXPORT_PPM " ++ path))
    (fun p => do requireWire ((← request p "STOP") == .ack) "canvas stop rejected")

end Lojita.Ownership.Tools.Web
