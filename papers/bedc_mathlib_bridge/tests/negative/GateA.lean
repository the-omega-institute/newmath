import BedcMathlibBridge.All
import BedcMathlibBridge.CI.Policy
import BedcGate.Audit

noncomputable def BedcMathlibBridge.Negative.choiceLeak : Nat :=
  Classical.choice (show Nonempty Nat from ⟨0⟩)

run_cmd do
  BedcGate.audit BedcMathlibBridge.CI.policy
