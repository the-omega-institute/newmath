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

end BEDC.Derived.GroupUp
