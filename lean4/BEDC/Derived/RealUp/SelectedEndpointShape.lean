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

theorem RealStreamClassifier_selected_endpoint_common_e1_tail_readback {x y : Nat -> BHist}
    {n : Nat} :
    RealStreamClassifier x y ->
      ∃ a b : BHist, hsame (x n) (BHist.e1 a) ∧ hsame (y n) (BHist.e1 b) ∧
        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified
  have shapes := RealStreamClassifier_selected_endpoint_e1_shapes (n := n) classified
  cases shapes.left with
  | intro a aShape =>
      cases shapes.right with
      | intro b bShape =>
          have tails :=
            RealStreamClassifier_selected_e1_pair_readback classified aShape.left bShape.left
          exact Exists.intro a
            (Exists.intro b
              (And.intro aShape.left
                (And.intro bShape.left
                  (And.intro tails.left (And.intro tails.right.left tails.right.right)))))

theorem RealStreamClassifier_transport_selected_endpoint_common_e1_tail_readback
    {x x' y y' : Nat -> BHist} {n : Nat} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          exists a b : BHist, hsame (x' n) (BHist.e1 a) ∧
            hsame (y' n) (BHist.e1 b) ∧ UnaryHistory a ∧ UnaryHistory b ∧
              hsame a b := by
  intro sameX sameY classified
  have shapes := RealStreamClassifier_selected_endpoint_e1_shapes (n := n) classified
  cases shapes.left with
  | intro a aShape =>
      cases shapes.right with
      | intro b bShape =>
          have sameLeft : hsame (x' n) (BHist.e1 a) :=
            hsame_trans (hsame_symm (sameX n)) aShape.left
          have sameRight : hsame (y' n) (BHist.e1 b) :=
            hsame_trans (hsame_symm (sameY n)) bShape.left
          have tails :=
            RealStreamClassifier_selected_e1_pair_readback classified aShape.left bShape.left
          exact Exists.intro a
            (Exists.intro b
              (And.intro sameLeft
                (And.intro sameRight
                  (And.intro tails.left (And.intro tails.right.left tails.right.right)))))

end BEDC.Derived.RealUp
