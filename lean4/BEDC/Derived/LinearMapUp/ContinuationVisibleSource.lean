import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonClassifier_continuation_visible_source_absurd {p q r h : BHist} :
    (Cont (BHist.e0 p) q r -> LinearMapSingletonClassifier r h -> False) ∧
      (Cont (BHist.e1 p) q r -> LinearMapSingletonClassifier r h -> False) := by
  constructor
  · intro continuation classified
    have emptyContinuation : Cont (BHist.e0 p) q BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    exact not_hsame_e0_empty (cont_empty_result_inversion emptyContinuation).left
  · intro continuation classified
    have emptyContinuation : Cont (BHist.e1 p) q BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    exact not_hsame_e1_empty (cont_empty_result_inversion emptyContinuation).left

end BEDC.Derived.LinearMapUp
