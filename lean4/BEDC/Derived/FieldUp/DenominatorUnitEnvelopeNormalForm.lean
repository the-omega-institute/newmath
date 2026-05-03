import BEDC.Derived.FieldUp.DenominatorUnitEnvelope

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem FieldRatDenominatorUnitEnvelopeClassifier_carrier_empty_split_iff {h k : BHist} :
    FieldRatDenominatorUnitEnvelopeClassifier h k ↔
      FieldRatDenominatorUnitEnvelopeCarrier h ∧ FieldRatDenominatorUnitEnvelopeCarrier k ∧
        hsame h k ∧
          ((RatHistoryCarrier h ∧ RatHistoryCarrier k) ∨
            (hsame h BHist.Empty ∧ hsame k BHist.Empty)) := by
  constructor
  · intro classified
    cases classified with
    | inl ratData =>
        exact And.intro (Or.inl ratData.left)
          (And.intro (Or.inl ratData.right.left)
            (And.intro ratData.right.right.right.right
              (Or.inl (And.intro ratData.left ratData.right.left))))
    | inr emptyData =>
        exact And.intro (Or.inr emptyData.left)
          (And.intro (Or.inr emptyData.right)
            (And.intro (hsame_trans emptyData.left (hsame_symm emptyData.right))
              (Or.inr emptyData)))
  · intro data
    cases data.right.right.right with
    | inl ratCarriers =>
        exact Or.inl
          (And.intro ratCarriers.left
            (And.intro ratCarriers.right
              (And.intro ratCarriers.left
                (And.intro ratCarriers.right data.right.right.left))))
    | inr emptyData =>
        exact Or.inr emptyData

end BEDC.Derived.FieldUp
