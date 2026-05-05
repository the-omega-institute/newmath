import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamPrefixClassifier_transported_selected_full_shape_readback_package
    {x x' y y' : Nat -> BHist} {m n : Nat} {a b zX zY : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      (forall i : Nat, hsame (x i) (x' i)) ->
        (forall i : Nat, hsame (y i) (y' i)) ->
          hsame (x' n) (BHist.e1 a) -> hsame (y' n) (BHist.e1 b) ->
            RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
              UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (x' n) ∧
                PositiveUnaryDenominator (y' n) ∧ UnaryHistory (x' n) ∧
                  UnaryHistory (y' n) ∧ (hsame (x' n) BHist.Empty -> False) ∧
                    (hsame (y' n) BHist.Empty -> False) ∧
                      (hsame (x' n) (BHist.e0 zX) -> False) ∧
                        (hsame (y' n) (BHist.e0 zY) -> False) := by
  intro classified sameX sameY sameLeft sameRight
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have endpointClassified : RatHistoryClassifier (x n) (y n) :=
    RealStreamPrefixClassifier_endpoint n prefixAtN
  have transported : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) endpointClassified
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight transported
  have tailReadback : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (x' n) ∧ PositiveUnaryDenominator (y' n) :=
    RatHistoryClassifier_positive_denominators transported
  have leftRows :
      UnaryHistory (x' n) ∧ (hsame (x' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (y' n) ∧ (hsame (y' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  constructor
  · exact displayed
  · constructor
    · exact tailReadback.left
    · constructor
      · exact tailReadback.right.left
      · constructor
        · exact tailReadback.right.right
        · constructor
          · exact positives.left
          · constructor
            · exact positives.right
            · constructor
              · exact leftRows.left
              · constructor
                · exact rightRows.left
                · constructor
                  · exact leftRows.right
                  · constructor
                    · exact rightRows.right
                    · constructor
                      · intro sameZero
                        exact PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero positives.left)
                      · intro sameZero
                        exact PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero positives.right)

theorem RealStreamClassifier_transported_selected_e1_tail_determinacy
    {x x' y y' : Nat -> BHist} {n : Nat} {a a' b b' : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> hsame (x' n) (BHist.e1 a) ->
          hsame (x' n) (BHist.e1 a') -> hsame (y' n) (BHist.e1 b) ->
            hsame (y' n) (BHist.e1 b') ->
              UnaryHistory a ∧ UnaryHistory a' ∧ UnaryHistory b ∧ UnaryHistory b' ∧
                hsame a a' ∧ hsame b b' ∧ hsame a b ∧ hsame a' b' := by
  intro sameX sameY classified sameLeft sameLeft' sameRight sameRight'
  have readAB :
      UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RealStreamClassifier_transport_selected_e1_pair_readback sameX sameY classified
      sameLeft sameRight
  have readA'B' :
      UnaryHistory a' ∧ UnaryHistory b' ∧ hsame a' b' :=
    RealStreamClassifier_transport_selected_e1_pair_readback sameX sameY classified
      sameLeft' sameRight'
  have sameAA' : hsame a a' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft')
  have sameBB' : hsame b b' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameRight) sameRight')
  exact And.intro readAB.left
    (And.intro readA'B'.left
      (And.intro readAB.right.left
        (And.intro readA'B'.right.left
          (And.intro sameAA'
            (And.intro sameBB' (And.intro readAB.right.right readA'B'.right.right))))))

theorem RealStreamClassifier_transported_selected_append_e1_tail_hsame_cancel
    {x x' y y' : Nat -> BHist} {n : Nat} {d e tailD tailE : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          hsame (x' n) (BHist.e1 (append d (BHist.e1 tailD))) ->
            hsame (y' n) (BHist.e1 (append e (BHist.e1 tailE))) ->
              hsame tailD tailE -> hsame d e := by
  intro sameX sameY classified sameLeft sameRight sameTail
  have displayed :
      RatHistoryClassifier (BHist.e1 (append d (BHist.e1 tailD)))
        (BHist.e1 (append e (BHist.e1 tailE))) :=
    RealStreamClassifier_transported_selected_e1_rat_classifier_readback sameX sameY
      classified sameLeft sameRight
  have readback :
      UnaryHistory (append d (BHist.e1 tailD)) ∧
        UnaryHistory (append e (BHist.e1 tailE)) ∧
          hsame (append d (BHist.e1 tailD)) (append e (BHist.e1 tailE)) :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  cases sameTail
  exact append_right_cancel (k := BHist.e1 tailD) readback.right.right

end BEDC.Derived.RealUp
