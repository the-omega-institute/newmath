import BEDC.Derived.FieldUp.RatContinuationOneSidedUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_commutative_semigroup_obstruction_package :
    (forall {d e r : BHist}, RatHistoryCarrier d -> RatHistoryCarrier e -> Cont d e r ->
      RatHistoryCarrier r) ∧
      (forall {d e f de ef l r : BHist}, RatHistoryCarrier d -> RatHistoryCarrier e ->
        RatHistoryCarrier f -> Cont d e de -> Cont e f ef -> Cont de f l ->
          Cont d ef r -> RatHistoryCarrier l ∧ RatHistoryCarrier r ∧
            RatHistoryClassifier l r) ∧
      (forall {d e r s : BHist}, RatHistoryCarrier d -> RatHistoryCarrier e ->
        Cont d e r -> Cont e d s -> RatHistoryClassifier r s) ∧
      (forall {u : BHist}, RatHistoryCarrier u ->
        (((forall {d r : BHist}, RatHistoryCarrier d -> Cont u d r ->
            RatHistoryClassifier r d) -> False) ∧
          ((forall {d r : BHist}, RatHistoryCarrier d -> Cont d u r ->
            RatHistoryClassifier r d) -> False))) := by
  constructor
  · intro d e r carrierD carrierE contDE
    exact RatHistoryCarrier_continuation_closed carrierD carrierE contDE
  · constructor
    · intro d e f de ef l r carrierD carrierE carrierF contDE contEF contLeft contRight
      have laws :=
        field_rat_denominator_continuation_semigroup_laws carrierD carrierE carrierF
          contDE contEF contLeft contRight
      exact ⟨laws.right.right.left, laws.right.right.right.left,
        ⟨laws.right.right.left, laws.right.right.right.left, laws.right.right.right.right⟩⟩
    · constructor
      · intro d e r s carrierD carrierE contDE contED
        exact field_rat_denominator_continuation_commutative_classifier carrierD carrierE
          contDE contED
      · intro u carrierU
        have noOneSided :=
          field_rat_denominator_continuation_no_one_sided_internal_unit carrierU
        exact ⟨noOneSided.right, noOneSided.left⟩

end BEDC.Derived.FieldUp
