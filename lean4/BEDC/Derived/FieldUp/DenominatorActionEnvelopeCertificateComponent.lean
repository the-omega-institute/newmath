import BEDC.Derived.FieldUp.RatDenominatorUnitEnvelopeContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RatupFieldupDenominatorActionEnvelopeCertificateComponent {h h' k k' r r' : BHist} :
    FieldRatDenominatorUnitEnvelopeClassifier h h' ->
      FieldRatDenominatorUnitEnvelopeClassifier k k' ->
        Cont h k r ->
          Cont h' k' r' ->
            FieldRatDenominatorUnitEnvelopeCarrier r ∧
              FieldRatDenominatorUnitEnvelopeCarrier r' ∧
                FieldRatDenominatorUnitEnvelopeClassifier r r' := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldRatDenominatorUnitEnvelopeClassifier
  intro classifiedH classifiedK leftContinuation rightContinuation
  have classifiedR :
      FieldRatDenominatorUnitEnvelopeClassifier r r' :=
    FieldRatDenominatorUnitEnvelopeClassifier_continuation_closed classifiedH classifiedK
      leftContinuation rightContinuation
  have carrierR : FieldRatDenominatorUnitEnvelopeCarrier r := by
    cases classifiedR with
    | inl ratData =>
        exact Or.inl ratData.left
    | inr emptyData =>
        exact Or.inr emptyData.left
  have carrierR' : FieldRatDenominatorUnitEnvelopeCarrier r' := by
    cases classifiedR with
    | inl ratData =>
        exact Or.inl ratData.right.left
    | inr emptyData =>
        exact Or.inr emptyData.right
  exact ⟨carrierR, carrierR', classifiedR⟩

end BEDC.Derived.FieldUp
