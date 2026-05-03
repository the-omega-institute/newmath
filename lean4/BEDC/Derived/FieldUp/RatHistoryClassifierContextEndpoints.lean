import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatHistoryClassifier_fieldSingletonEmptyNonZero_context_endpoints {L R h k : BHist} :
    RatHistoryClassifier h k ->
      fieldSingletonEmptyNonZero (append L h) ∧ fieldSingletonEmptyNonZero (append R k) := by
  intro classified
  have endpointNonempty := RatHistoryClassifier_endpoints_not_empty classified
  constructor
  · intro singleton
    have split := append_eq_empty_iff.mp singleton.left
    exact endpointNonempty.left split.right
  · intro singleton
    have split := append_eq_empty_iff.mp singleton.left
    exact endpointNonempty.right split.right

end BEDC.Derived.FieldUp
