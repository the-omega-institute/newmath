import BedcMathlibBridge.All
import BedcMathlibBridge.CI.Policy
import BedcGate.Audit

namespace BedcMathlibBridge.Negative

inductive MissingAttrCarrier where
  | mk : Nat -> MissingAttrCarrier

instance : Mul MissingAttrCarrier where
  mul
    | .mk a, .mk b => .mk (a * b)

end BedcMathlibBridge.Negative

def negativePolicy : BedcGate.Policy :=
  { BedcMathlibBridge.CI.policy with
    trackedTypeHeads :=
      BedcMathlibBridge.CI.policy.trackedTypeHeads.push
        `BedcMathlibBridge.Negative.MissingAttrCarrier }

run_cmd do
  BedcGate.audit negativePolicy
