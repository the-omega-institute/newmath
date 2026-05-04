import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RingSingletonClassifier_cont_result_empty_iff {h k p r : BHist} :
    RingSingletonClassifier h k -> Cont h p r ->
      (hsame r BHist.Empty ↔ RingSingletonCarrier p) := by
  intro classified rel
  constructor
  · intro resultEmpty
    have emptyRel : Cont h p BHist.Empty :=
      cont_result_hsame_transport rel resultEmpty
    exact (cont_empty_result_inversion emptyRel).right
  · intro pEmpty
    exact cont_deterministic rel (by
      cases classified.left
      cases pEmpty
      exact cont_right_unit BHist.Empty)

end BEDC.Derived.RingUp
