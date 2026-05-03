import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_continuation_visible_result_absurd {P Q r : BHist} :
    GroupSingletonClassifier P Q ->
      (Cont P Q (BHist.e0 r) -> False) ∧ (Cont P Q (BHist.e1 r) -> False) := by
  intro classified
  constructor
  · intro continuation
    have resultEmpty : hsame (BHist.e0 r) BHist.Empty :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact not_hsame_e0_empty resultEmpty
  · intro continuation
    have resultEmpty : hsame (BHist.e1 r) BHist.Empty :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact not_hsame_e1_empty resultEmpty

theorem GroupSingletonClassifier_continuation_result_left_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonClassifier P Q <-> GroupSingletonClassifier R P) := by
  intro continuation
  constructor
  · intro classified
    have resultCarrier : GroupSingletonCarrier R :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact And.intro resultCarrier
      (And.intro classified.left (hsame_trans resultCarrier (hsame_symm classified.left)))
  · intro resultClassified
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation resultClassified.left
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

end BEDC.Derived.GroupUp
