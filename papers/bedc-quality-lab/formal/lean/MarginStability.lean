import Mathlib.Data.Fintype.Basic

namespace MarginStability

inductive ThresholdSide where
  | below
  | above
  deriving DecidableEq, Repr

def allSides : List ThresholdSide :=
  [ThresholdSide.below, ThresholdSide.above]

theorem side_mem_allSides (side : ThresholdSide) : side ∈ allSides := by
  cases side <;> simp [allSides]

theorem allSides_complete (side : ThresholdSide) :
    side = ThresholdSide.below ∨ side = ThresholdSide.above := by
  cases side <;> simp

inductive MarginCertificate : ThresholdSide → ThresholdSide → Prop where
  | below : MarginCertificate ThresholdSide.below ThresholdSide.below
  | above : MarginCertificate ThresholdSide.above ThresholdSide.above

def markStable (before after : ThresholdSide) : Prop :=
  after = before

def perturbationWithinMargin (before after : ThresholdSide) : Prop :=
  MarginCertificate before after

theorem below_certificate :
    perturbationWithinMargin ThresholdSide.below ThresholdSide.below := by
  exact MarginCertificate.below

theorem above_certificate :
    perturbationWithinMargin ThresholdSide.above ThresholdSide.above := by
  exact MarginCertificate.above

theorem mark_stable_of_margin {before after : ThresholdSide}
    (h : MarginCertificate before after) :
    markStable before after := by
  cases h <;> rfl

theorem margin_certificate_same_side {before after : ThresholdSide}
    (h : MarginCertificate before after) :
    before = after := by
  cases h <;> rfl

theorem stable_side_same {before after : ThresholdSide}
    (h : MarginCertificate before after) :
    before = after ∧ after = before := by
  constructor
  · exact margin_certificate_same_side h
  · exact mark_stable_of_margin h

end MarginStability
