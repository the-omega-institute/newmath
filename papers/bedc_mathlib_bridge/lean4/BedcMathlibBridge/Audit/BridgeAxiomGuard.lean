import BedcMathlibBridge.All
import BedcGate.Audit

namespace BedcMathlibBridge.Audit.BridgeAxiomGuard

open Lean Elab Command

def policy : BedcGate.Policy where
  bridgeDeclPrefix := `BedcMathlibBridge
  bridgeModulePrefix := `BedcMathlibBridge
  bedcDeclPrefix := `BEDC
  bedcModulePrefix := `BEDC
  trackedTypeHeads := #[]
  operationClasses := #[]
  ignoredDeclPrefixes := #[
    `BedcMathlibBridge.Audit
  ]

run_cmd do
  let audited ← BedcGate.auditGateA policy
  logInfo m!"[bridge-axioms] audited {audited} bridge declaration(s)"

end BedcMathlibBridge.Audit.BridgeAxiomGuard
