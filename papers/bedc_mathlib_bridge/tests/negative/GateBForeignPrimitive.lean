import BedcGate.Provenance
import BedcGate.Audit

def BedcMathlibBridge.Negative.foreignPrimitiveAnchor : Unit :=
  let _ : (Nat.zero = Nat.zero) := rfl
  ()

@[bedcDerived Nat.zero]
def BedcMathlibBridge.Negative.foreignPrimitiveProbe : Unit :=
  let _ := BedcMathlibBridge.Negative.foreignPrimitiveAnchor
  ()

def negativePolicy : BedcGate.Policy where
  bridgeDeclPrefix := `BedcMathlibBridge
  bridgeModulePrefix := `BedcMathlibBridge
  bedcDeclPrefix := `BEDC
  bedcModulePrefix := `BEDC
  trackedTypeHeads := #[]
  operationClasses := #[]

run_cmd do
  BedcGate.audit negativePolicy
