import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexHistoryCarrier_components_nonempty {h : BHist} :
    ComplexHistoryCarrier h ->
      ∃ real imag : BHist,
        RatUp.RatHistoryCarrier real ∧ RatUp.RatHistoryCarrier imag ∧ Cont real imag h ∧
          (hsame real BHist.Empty -> False) ∧ (hsame imag BHist.Empty -> False) := by
  intro carrier
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (And.intro realCarrier
                        (And.intro imagCarrier
                          (And.intro cont
                            (And.intro
                              (RatUp.RatHistoryCarrier_not_empty realCarrier)
                              (RatUp.RatHistoryCarrier_not_empty imagCarrier))))))

theorem ComplexHistoryClassifier_endpoint_e1_shapes {h k : BHist} :
    ComplexHistoryClassifier h k ->
      (∃ ht : BHist, h = BHist.e1 ht ∧ UnaryHistory ht) ∧
        (∃ kt : BHist, k = BHist.e1 kt ∧ UnaryHistory kt) := by
  intro classified
  have endpoints := ComplexHistoryClassifier_nonempty_endpoints classified
  constructor
  · exact unary_history_nonempty_e1_tail (ComplexHistoryCarrier_unary classified.left) endpoints.left
  · exact
      unary_history_nonempty_e1_tail
        (ComplexHistoryCarrier_unary classified.right.left) endpoints.right

end BEDC.Derived.ComplexUp
