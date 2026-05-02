import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_comm_closed {P Q left right : BHist} :
    FieldSingletonClassifier P Q -> Cont P Q left -> Cont Q P right ->
      FieldSingletonClassifier left right := by
  intro classified leftContinuation rightContinuation
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame classified.left classified.right.left leftContinuation
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame classified.right.left classified.left rightContinuation
      (cont_right_unit BHist.Empty)
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem FieldSingletonCarrier_continuation_closed {P Q R : BHist} :
    FieldSingletonCarrier P -> FieldSingletonCarrier Q -> Cont P Q R -> FieldSingletonCarrier R := by
  intro carrierP carrierQ continuation
  exact cont_respects_hsame carrierP carrierQ continuation (cont_right_unit BHist.Empty)

theorem FieldSingletonClassifier_continuation_result_classifier {P Q R : BHist} :
    FieldSingletonClassifier P Q -> Cont P Q R -> FieldSingletonClassifier R BHist.Empty := by
  intro classified continuation
  have resultCarrier : FieldSingletonCarrier R :=
    FieldSingletonCarrier_continuation_closed classified.left classified.right.left continuation
  exact And.intro resultCarrier (And.intro (hsame_refl BHist.Empty) resultCarrier)

theorem FieldSingletonClassifier_continuation_closed {P P' Q Q' left right : BHist} :
    FieldSingletonClassifier P P' -> FieldSingletonClassifier Q Q' -> Cont P Q left ->
      Cont P' Q' right -> FieldSingletonClassifier left right := by
  intro classifiedP classifiedQ leftContinuation rightContinuation
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame classifiedP.left classifiedQ.left leftContinuation
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame classifiedP.right.left classifiedQ.right.left rightContinuation
      (cont_right_unit BHist.Empty)
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem FieldSingletonClassifier_continuation_endpoint_split_iff {P Q R : BHist} :
    Cont P Q R ->
      (FieldSingletonClassifier P Q <->
        FieldSingletonCarrier P /\ FieldSingletonCarrier Q /\ FieldSingletonCarrier R) := by
  intro continuation
  constructor
  · intro classified
    have resultCarrier : FieldSingletonCarrier R :=
      FieldSingletonCarrier_continuation_closed classified.left classified.right.left continuation
    exact And.intro classified.left (And.intro classified.right.left resultCarrier)
  · intro endpoints
    exact And.intro endpoints.left
      (And.intro endpoints.right.left
        (hsame_trans endpoints.left (hsame_symm endpoints.right.left)))

end BEDC.Derived.FieldUp
