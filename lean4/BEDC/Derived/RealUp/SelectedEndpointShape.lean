import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealStreamClassifier_selected_endpoint_e1_shapes {x y : Nat -> BHist} {n : Nat} :
    RealStreamClassifier x y ->
      (∃ xt : BHist, x n = BHist.e1 xt ∧ UnaryHistory xt) ∧
        (∃ yt : BHist, y n = BHist.e1 yt ∧ UnaryHistory yt) := by
  intro classified
  have endpoints :=
    RealStreamClassifier_selected_positive_unary_nonempty_package (n := n) classified
  constructor
  · exact
      unary_history_nonempty_e1_tail endpoints.right.right.left
        endpoints.right.right.right.right.left
  · exact
      unary_history_nonempty_e1_tail endpoints.right.right.right.left
        endpoints.right.right.right.right.right

end BEDC.Derived.RealUp
