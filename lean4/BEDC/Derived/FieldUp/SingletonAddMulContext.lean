import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonAddMul_context_continuation_result_carrier {L R a b c d out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonMul c d) R) out ->
        FieldSingletonCarrier out := by
  intro carrierL carrierR continuation
  unfold FieldSingletonCarrier at carrierL carrierR
  unfold FieldSingletonAdd FieldSingletonMul at continuation
  cases carrierL
  cases carrierR
  exact cont_deterministic continuation (cont_right_unit BHist.Empty)

end BEDC.Derived.FieldUp
