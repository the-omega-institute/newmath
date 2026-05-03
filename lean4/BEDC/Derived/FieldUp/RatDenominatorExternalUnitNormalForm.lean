import BEDC.Derived.FieldUp.RatExternalUnitSeparation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_external_unit_normal_form {u : BHist} :
    (((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ↔
        (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d)) ∧
      (((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ∨
          (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d)) ↔
        hsame u BHist.Empty) ∧
      (RatHistoryCarrier u ->
        ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ∨
          (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d)) ->
          False)) := by
  have package := field_rat_denominator_external_unit_separation_package (u := u)
  constructor
  · constructor
    · intro rightLaw
      exact package.right.left.mpr (package.left.mp rightLaw)
    · intro leftLaw
      exact package.left.mpr (package.right.left.mp leftLaw)
  · constructor
    · constructor
      · intro oneSided
        cases oneSided with
        | inl rightLaw =>
            exact Iff.mp package.left rightLaw
        | inr leftLaw =>
            exact Iff.mp package.right.left leftLaw
      · intro emptyEndpoint
        exact Or.inl (package.left.mpr emptyEndpoint)
    · intro carrierU oneSided
      have exclusion := package.right.right carrierU
      cases oneSided with
      | inl rightLaw =>
          exact exclusion.left rightLaw
      | inr leftLaw =>
          exact exclusion.right leftLaw

end BEDC.Derived.FieldUp
