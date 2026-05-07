import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatStreamNameFiniteWindowClassifier_empty_vacuity {s t : BHist -> BHist} :
    RatStreamNameFiniteWindowClassifier s t ProbeBundle.Bnil := by
  intro n member _nUnary
  exact False.elim (inBundle_nil_elim member)

end BEDC.Derived.StreamNameUp
