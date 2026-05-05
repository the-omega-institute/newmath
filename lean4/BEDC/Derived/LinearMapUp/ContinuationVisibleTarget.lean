import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonClassifier_continuation_visible_target_absurd {p q r h : BHist} :
    (Cont q (BHist.e0 p) r -> LinearMapSingletonClassifier r h -> False) ∧
      (Cont q (BHist.e1 p) r -> LinearMapSingletonClassifier r h -> False) := by
  constructor
  · intro continuation classified
    have emptyContinuation : Cont q (BHist.e0 p) BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    exact not_hsame_e0_empty (cont_empty_result_inversion emptyContinuation).right
  · intro continuation classified
    have emptyContinuation : Cont q (BHist.e1 p) BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    exact not_hsame_e1_empty (cont_empty_result_inversion emptyContinuation).right

end BEDC.Derived.LinearMapUp
