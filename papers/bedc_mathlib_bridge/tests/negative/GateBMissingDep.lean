import BedcGate.Provenance
import BEDC.Derived.PrimeUp

def BedcMathlibBridge.Negative.unrelatedAnchor : Unit :=
  let _ : (Nat.zero = Nat.zero) := rfl
  ()

@[bedcDerived BEDC.Derived.PrimeUp.NatMul]
def BedcMathlibBridge.Negative.missingDependencyProbe : Unit :=
  let _ := BedcMathlibBridge.Negative.unrelatedAnchor
  ()
