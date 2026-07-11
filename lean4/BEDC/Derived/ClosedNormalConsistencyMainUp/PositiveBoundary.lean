import BEDC.Derived.ClosedNormalConsistencyMainUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedNormalConsistencyMainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedNormalConsistencyMainCarrier_positive_boundary
    {T F L B R «public» : BHist}
    (falseTyping : Cont T F L)
    (endpointRoute : Cont L B R)
    (publicRead : Cont R F «public») :
    hsame «public» (append T (append F (append B F))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases falseTyping
  cases endpointRoute
  cases publicRead
  exact (append_assoc (append T F) B F).trans (append_assoc T F (append B F))

end BEDC.Derived.ClosedNormalConsistencyMainUp
