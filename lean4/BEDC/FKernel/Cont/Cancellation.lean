import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_right_cancel_hsame_result {h h' k r r' : BHist} :
    Cont h k r -> Cont h' k r' -> hsame r r' -> hsame h h' := by
  intro left right same
  apply append_right_cancel (k := k)
  exact left.symm.trans (same.trans right)

end BEDC.FKernel.Cont
