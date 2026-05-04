import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ComplexHistoryClassifier_component_target_hsame_transport
    {real imag real' imag' h k k' : BHist} :
    RatUp.RatHistoryClassifier real real' -> RatUp.RatHistoryClassifier imag imag' ->
      Cont real imag h -> Cont real' imag' k -> hsame k k' ->
        ComplexHistoryClassifier h k' := by
  intro realClassifier imagClassifier sourceCont targetCont sameTarget
  have shiftedTarget : Cont real' imag' k' :=
    cont_result_hsame_transport targetCont sameTarget
  exact ComplexHistoryClassifier_component_classifier_intro
    realClassifier imagClassifier sourceCont shiftedTarget

end BEDC.Derived.ComplexUp
