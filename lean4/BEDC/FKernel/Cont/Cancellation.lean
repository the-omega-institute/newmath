import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_right_cancel_hsame_result {h h' k r r' : BHist} :
    Cont h k r -> Cont h' k r' -> hsame r r' -> hsame h h' := by
  intro left right same
  apply append_right_cancel (k := k)
  exact left.symm.trans (same.trans right)

theorem cont_hsame_transport {h h' k k' r r' : BHist} :
    hsame h h' → hsame k k' → hsame r r' → Cont h k r → Cont h' k' r' := by
  intro sameH sameK sameR hcont
  cases sameH
  cases sameK
  exact BEDC.FKernel.Cont.cont_result_hsame_transport hcont sameR

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

theorem continuation_right_cancellation {h h' k r : BHist} :
    Cont h k r -> Cont h' k r -> hsame h h' := by
  intro left right
  exact cont_right_cancel left right

theorem cont_mutual_extension_hsame {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h -> hsame h k := by
  intro left right
  have cycle : Cont h (append leftTail rightTail) h := by
    exact right.trans
      ((congrArg (fun x => append x rightTail) left).trans
        (append_assoc h leftTail rightTail))
  have tailEmpty : hsame (append leftTail rightTail) BHist.Empty :=
    cont_right_unit_unique cycle
  have leftEmpty : leftTail = BHist.Empty := (append_eq_empty_iff.mp tailEmpty).left
  cases leftEmpty
  exact left.symm

theorem cont_cancel_hsame_left_context {a a' b d r r' : BHist} :
    Cont a b r -> Cont a' d r' -> hsame a a' -> hsame r r' -> hsame b d := by
  intro left right sameContext sameResult
  cases sameContext
  cases sameResult
  exact cont_left_cancel left right

end BEDC.FKernel.Cont
