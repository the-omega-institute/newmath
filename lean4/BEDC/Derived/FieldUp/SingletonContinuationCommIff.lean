import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_comm_iff {P Q L R : BHist} :
    Cont P Q L -> Cont Q P R ->
      (FieldSingletonClassifier L R ↔ FieldSingletonClassifier P Q) := by
  intro leftRel rightRel
  constructor
  · intro classifiedLR
    have leftEmpty : hsame L BHist.Empty := classifiedLR.left
    have emptyLeftRel : Cont P Q BHist.Empty :=
      cont_result_hsame_transport leftRel leftEmpty
    have inputParts := cont_empty_result_inversion emptyLeftRel
    exact And.intro inputParts.left
      (And.intro inputParts.right
        (hsame_trans inputParts.left (hsame_symm inputParts.right)))
  · intro classifiedPQ
    have leftCarrier : FieldSingletonCarrier L :=
      cont_respects_hsame classifiedPQ.left classifiedPQ.right.left leftRel
        (cont_left_unit BHist.Empty)
    have rightCarrier : FieldSingletonCarrier R :=
      cont_respects_hsame classifiedPQ.right.left classifiedPQ.left rightRel
        (cont_left_unit BHist.Empty)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem fieldSingletonEmptyNonZero_continuation_comm_iff {P Q left right : BHist} :
    Cont P Q left -> Cont Q P right ->
      (fieldSingletonEmptyNonZero left ↔ fieldSingletonEmptyNonZero right) := by
  intro leftRel rightRel
  constructor
  · intro leftNonzero
    apply Iff.mpr fieldSingletonEmptyNonZero_empty_endpoint_complement_iff
    intro rightEmpty
    have rightEmptyRel : Cont Q P BHist.Empty :=
      cont_result_hsame_transport rightRel rightEmpty
    have endpoints := cont_empty_result_inversion rightEmptyRel
    have leftEmpty : hsame left BHist.Empty := by
      cases endpoints.left
      cases endpoints.right
      exact cont_left_unit_result leftRel
    exact fieldSingletonEmptyNonZero_empty_endpoint_absurd leftEmpty leftNonzero
  · intro rightNonzero
    apply Iff.mpr fieldSingletonEmptyNonZero_empty_endpoint_complement_iff
    intro leftEmpty
    have leftEmptyRel : Cont P Q BHist.Empty :=
      cont_result_hsame_transport leftRel leftEmpty
    have endpoints := cont_empty_result_inversion leftEmptyRel
    have rightEmpty : hsame right BHist.Empty := by
      cases endpoints.left
      cases endpoints.right
      exact cont_left_unit_result rightRel
    exact fieldSingletonEmptyNonZero_empty_endpoint_absurd rightEmpty rightNonzero

end BEDC.Derived.FieldUp
