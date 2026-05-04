import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RealConstantHistoryClassifier_append_common_head_cancel {head d e : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append head d)) (BHist.e1 (append head e)) ->
      hsame d e := by
  intro classified
  have rational :
      RatHistoryClassifier (append head d) (append head e) :=
    Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
  exact append_left_cancel (h := head) rational.right.right

theorem RealConstantHistoryClassifier_append_common_context_cancel {left right d e : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append left (append d right)))
      (BHist.e1 (append left (append e right))) ->
        hsame d e := by
  intro classified
  have withoutLeft : hsame (append d right) (append e right) :=
    RealConstantHistoryClassifier_append_common_head_cancel (head := left) classified
  exact append_right_cancel (k := right) withoutLeft

end BEDC.Derived.RealUp
