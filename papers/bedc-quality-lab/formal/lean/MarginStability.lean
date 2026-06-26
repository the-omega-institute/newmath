import Mathlib.Data.Fintype.Basic

namespace MarginStability

inductive ThresholdSide where
  | below
  | above
  deriving DecidableEq, Repr

inductive MarginCertificate : ThresholdSide → ThresholdSide → Prop where
  | below : MarginCertificate ThresholdSide.below ThresholdSide.below
  | above : MarginCertificate ThresholdSide.above ThresholdSide.above

def markStable (before after : ThresholdSide) : Prop :=
  after = before

theorem mark_stable_of_margin {before after : ThresholdSide}
    (h : MarginCertificate before after) :
    markStable before after := by
  cases h <;> rfl

end MarginStability
