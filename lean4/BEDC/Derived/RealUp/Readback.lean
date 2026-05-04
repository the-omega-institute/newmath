import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.DenominatorAppendDecomposition

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_transport_selected_e1_pair_readback
    {x x' y y' : Nat -> BHist} {n : Nat} {a b : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          hsame (x' n) (BHist.e1 a) ->
            hsame (y' n) (BHist.e1 b) ->
              UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro sameX sameY classified sameLeft sameRight
  have hPrefix : RealStreamPrefixClassifier x y n :=
    (RealStreamClassifier_finite_prefix_exactness.mp classified) n
  have transported : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  exact RealStreamPrefixClassifier_e1_pair_readback transported sameLeft sameRight

theorem RealConstantHistoryClassifier_append_e1_tail_unary_readback
    {d e tailD tailE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
      (BHist.e1 (append e (BHist.e1 tailE))) ->
      UnaryHistory d ∧ UnaryHistory tailD ∧ UnaryHistory e ∧ UnaryHistory tailE ∧
        hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) := by
  intro classified
  have rational :
      RatHistoryClassifier (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mp classified
  have positives := RatHistoryClassifier_positive_denominators rational
  have leftUnary :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.left
  have rightUnary :=
    PositiveUnaryDenominator_append_e1_right_iff.mp positives.right
  exact And.intro leftUnary.left
    (And.intro leftUnary.right
      (And.intro rightUnary.left (And.intro rightUnary.right rational.right.right)))

end BEDC.Derived.RealUp
