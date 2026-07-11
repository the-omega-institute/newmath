import BEDC.Derived.ClosedNormalConsistencyWitnessUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedNormalConsistencyWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedNormalConsistencyWitnessFalseExclusion_factorization
    {T F L E B R «public» : BHist}
    (typingRoute : Cont T F L)
    (closedEndpointRoute : Cont L E B)
    (falseExclusionRoute : Cont B R «public») :
    hsame «public» (append T (append F (append E R))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases typingRoute
  cases closedEndpointRoute
  cases falseExclusionRoute
  exact (append_assoc (append T F) E R).trans (append_assoc T F (append E R))

end BEDC.Derived.ClosedNormalConsistencyWitnessUp
