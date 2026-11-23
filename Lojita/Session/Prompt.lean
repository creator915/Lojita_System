import Lojita.Session.PromptTemplates
import Lojita.Session.Context

namespace Lojita.Session
open Lojita.Harness Lojita.Kernel Lojita.Transport Lojita.Store

def nodePrompt (req : AIRequest) : String :=
  let t := req.task
  let spec := t.delta.newIface
  let seeds := spec.units.filter (fun u => u.kind != .axiomDecl)
  String.intercalate "\n" [nodeTemplate,"CURRENT CODE",renderLeanMod req.old,"SPECIFICATION",renderLeanMod t.delta.newIface,
    "LOCKED SEEDS",renderLeanMod {spec with units := seeds},
    "PREVIOUS INTERFACE",(encodeIface t.delta.oldIface).canonical,
    "ANCESTORS",String.intercalate "\n" ((readableAncestors t).map renderLeanMod),
    "ALLOWED DIRECT IMPORTS",String.intercalate " " ((t.allowedAncestors.getD (t.baseModules.map (·.modName))).map toString),
    "SAVED CHILDREN",String.intercalate " " (req.home.toList.flatMap fun h => h.children.map Prod.fst),
    "LIFT",String.intercalate "\n" (t.lifts.map fun (_,s) => (encodeLiftSpec s).canonical),
    "POLY-TRANSPORT",String.intercalate "\n" (t.transports.map fun (_,s) => (encodeTransportSpec s).canonical),
    "MEMORY",(encodeMemory req.memory).canonical,t.contextText,"TRANSIENT DIAGNOSTIC",
    (req.diagnostic.map toString).getD ""]

def sessionPrompt (goal : String) (ref : RefSpec) (trees memory : List String) (diagnostic : String) :=
  String.intercalate "\n" [sessionTemplate,"GOAL",goal,"REFERENCE TARGET",(encodeRefSpec ref).canonical,
    "SEALED TREES",String.intercalate "\n" trees,"RECENT ACTION OUTCOMES",String.intercalate "\n" (memory.reverse.take 4).reverse,
    "SESSION MEMORY (session-memory.sexp)",(SExpr.list (memory.map .str)).canonical,"TRANSIENT DIAGNOSTIC",diagnostic]

end Lojita.Session
