import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_right_cancel_hsame_result {h h' k r r' : BHist} :
    Cont h k r -> Cont h' k r' -> hsame r r' -> hsame h h' := by
  intro left right same
  apply append_right_cancel (k := k)
  exact left.symm.trans (same.trans right)

theorem cont_cancel_common_context {a b c d ab ad left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont a d ad -> Cont ad c right ->
      hsame left right -> hsame b d := by
  intro abDef leftDef adDef rightDef same
  cases abDef
  cases adDef
  have commonSuffix : hsame (append a b) (append a d) := by
    apply append_right_cancel (k := c)
    exact leftDef.symm.trans (same.trans rightDef)
  exact append_left_cancel (h := a) commonSuffix

end BEDC.FKernel.Cont
