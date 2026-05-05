import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Cont.Units
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.PreorderUp

theorem NetworkFlowEmptyBackwardAccounting_cut_flow_below_value {V B X : BHist} :
    Cont V B X -> hsame B BHist.Empty -> PreorderPrefixLE X V := by
  intro accounting backwardEmpty
  have transported : Cont V BHist.Empty X :=
    cont_hsame_transport (hsame_refl V) backwardEmpty (hsame_refl X) accounting
  have sameXV : hsame X V :=
    cont_right_unit_result transported
  exact PreorderPrefixLE_of_hsame sameXV

end BEDC.Derived.NetworkFlowUp
