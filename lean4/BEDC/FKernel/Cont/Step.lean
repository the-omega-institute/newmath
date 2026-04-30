import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_e0_result_witness {h k r : BHist} :
    Cont h (BHist.e0 k) r -> exists r0 : BHist, r = BHist.e0 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.left hcont

end BEDC.FKernel.Cont
