import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_external_boundary_laws :
    (RatHistoryCarrier BHist.Empty -> False) ∧
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont d BHist.Empty r ->
        RatHistoryClassifier r d) ∧
      (∀ {d s : BHist}, RatHistoryCarrier d -> Cont BHist.Empty d s ->
        RatHistoryClassifier s d) ∧
      (∀ {d e f de ef left right : BHist}, RatHistoryCarrier d -> RatHistoryCarrier e ->
        RatHistoryCarrier f -> Cont d e de -> Cont de f left -> Cont e f ef ->
          Cont d ef right -> RatHistoryClassifier left right) := by
  constructor
  · intro emptyCarrier
    exact RatHistoryCarrier_not_empty emptyCarrier (hsame_refl BHist.Empty)
  constructor
  · intro d r carrierD rightEmpty
    have sameRD : hsame r d :=
      cont_deterministic rightEmpty (cont_right_unit d)
    exact ⟨RatHistoryCarrier_hsame_transport (hsame_symm sameRD) carrierD, carrierD, sameRD⟩
  constructor
  · intro d s carrierD leftEmpty
    have sameSD : hsame s d :=
      cont_left_unit_result leftEmpty
    exact ⟨RatHistoryCarrier_hsame_transport (hsame_symm sameSD) carrierD, carrierD, sameSD⟩
  · intro d e f de ef left right carrierD carrierE carrierF contDE contLeft contEF contRight
    have laws :=
      field_rat_denominator_continuation_semigroup_laws carrierD carrierE carrierF contDE contEF
        contLeft contRight
    exact ⟨laws.right.right.left, laws.right.right.right.left, laws.right.right.right.right⟩

end BEDC.Derived.FieldUp
