import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealupFiniteWindowExhaustionObligation {h k d e : BHist} :
    RealConstantHistoryClassifier h k ->
      hsame h (BHist.e1 (BHist.e1 d)) ->
        hsame k (BHist.e1 (BHist.e1 e)) ->
          RatHistoryClassifier (BHist.e1 d) (BHist.e1 e) ∧
            UnaryHistory d ∧ UnaryHistory e ∧ hsame d e := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory
  intro classified sameH sameK
  have displayed :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 d)) (BHist.e1 (BHist.e1 e)) :=
    RealConstantHistoryClassifier_endpoint_transport sameH sameK classified
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 d) (BHist.e1 e) :=
    RealConstantHistoryClassifier_e1_iff_rat.mp displayed
  have tailRows :
      UnaryHistory d ∧ UnaryHistory e ∧ hsame d e :=
    RealConstantHistoryClassifier_e1_pair_readback classified sameH sameK
  exact ⟨ratClassifier, tailRows.left, tailRows.right.left, tailRows.right.right⟩

end BEDC.Derived.RealUp
