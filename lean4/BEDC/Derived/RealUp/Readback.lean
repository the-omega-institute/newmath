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

theorem RealConstantHistoryClassifier_append_common_head_e1_tail_readback
    {left d e tailD tailE : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append left (append d (BHist.e1 tailD))))
      (BHist.e1 (append left (append e (BHist.e1 tailE)))) ->
      hsame tailD tailE ->
        UnaryHistory left ∧ UnaryHistory d ∧ UnaryHistory e ∧ UnaryHistory tailD ∧
          UnaryHistory tailE ∧ hsame d e := by
  intro classified sameTail
  have leftAssoc :
      hsame (BHist.e1 (append left (append d (BHist.e1 tailD))))
        (BHist.e1 (append (append left d) (BHist.e1 tailD))) := by
    exact congrArg BHist.e1 (append_assoc left d (BHist.e1 tailD)).symm
  have rightAssoc :
      hsame (BHist.e1 (append left (append e (BHist.e1 tailE))))
        (BHist.e1 (append (append left e) (BHist.e1 tailE))) := by
    exact congrArg BHist.e1 (append_assoc left e (BHist.e1 tailE)).symm
  have displayed :
      RealConstantHistoryClassifier (BHist.e1 (append (append left d) (BHist.e1 tailD)))
        (BHist.e1 (append (append left e) (BHist.e1 tailE))) :=
    RealConstantHistoryClassifier_endpoint_transport leftAssoc rightAssoc classified
  have readback :=
    RealConstantHistoryClassifier_append_e1_tail_unary_readback displayed
  have leftFactors :
      UnaryHistory left ∧ UnaryHistory d :=
    unary_append_factors_iff_result.mpr readback.left
  have rightFactors :
      UnaryHistory left ∧ UnaryHistory e :=
    unary_append_factors_iff_result.mpr readback.right.right.left
  have sameHeaded : hsame (append left d) (append left e) := by
    cases sameTail
    exact append_right_cancel (k := BHist.e1 tailD) readback.right.right.right.right
  have sameDE : hsame d e :=
    append_left_cancel (h := left) sameHeaded
  exact And.intro leftFactors.left
    (And.intro leftFactors.right
      (And.intro rightFactors.right
        (And.intro readback.right.left
          (And.intro readback.right.right.right.left sameDE))))

theorem RealStreamClassifier_selected_append_e1_tail_hsame_cancel
    {x y : Nat -> BHist} {n : Nat} {d e tailD tailE : BHist} :
    RealStreamClassifier x y ->
      hsame (x n) (BHist.e1 (append d (BHist.e1 tailD))) ->
        hsame (y n) (BHist.e1 (append e (BHist.e1 tailE))) ->
          hsame tailD tailE -> hsame d e := by
  intro classified sameLeft sameRight sameTail
  have pointClassified : RatHistoryClassifier (x n) (y n) :=
    classified n
  have displayed :
      RatHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
        (BHist.e1 (append e (BHist.e1 tailE))) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight pointClassified
  have readback :
      UnaryHistory (append d (BHist.e1 tailD)) ∧
        UnaryHistory (append e (BHist.e1 tailE)) ∧
          hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  cases sameTail
  exact append_right_cancel (k := BHist.e1 tailD) readback.right.right

end BEDC.Derived.RealUp
