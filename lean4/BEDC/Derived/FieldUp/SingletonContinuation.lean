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

end BEDC.Derived.FieldUp
