import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

def RealUnaryOffsetLe (k w : BHist) : Prop :=
  UnaryHistory k ∧ ∃ tau : BHist, UnaryHistory tau ∧ Cont k tau w

def RealUnaryStreamWindowClassifier (s t : BHist -> BHist) (a w : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory w ∧
    forall k : BHist, RealUnaryOffsetLe k w ->
      RatHistoryClassifier (s (append a k)) (t (append a k))

theorem RatStreamNameClassifier_real_unary_window_coverage {s t : BHist -> BHist}
    {a w : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> RealUnaryStreamWindowClassifier s t a w := by
  intro _carrierS _carrierT classified aUnary wUnary
  exact ⟨aUnary, wUnary,
    fun k offset => classified.right.right (append a k)
      (unary_append_closed aUnary offset.left)⟩

def RealStreamWindowClassifier (x y : Nat -> BHist) (n m : Nat) : Prop :=
  forall k : Nat, k <= m -> RatHistoryClassifier (x (n + k)) (y (n + k))

theorem RealStreamWindowClassifier_selected_full_shape_readback_package
    {x y : Nat -> BHist} {n m k : Nat} {a b zX zY : BHist} :
    RealStreamWindowClassifier x y n m -> k <= m -> hsame (x (n + k)) (BHist.e1 a) ->
      hsame (y (n + k)) (BHist.e1 b) ->
        RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
          UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (x (n + k)) ∧
            PositiveUnaryDenominator (y (n + k)) ∧ UnaryHistory (x (n + k)) ∧
              UnaryHistory (y (n + k)) ∧ (hsame (x (n + k)) BHist.Empty -> False) ∧
                (hsame (y (n + k)) BHist.Empty -> False) ∧
                  (hsame (x (n + k)) (BHist.e0 zX) -> False) ∧
                    (hsame (y (n + k)) (BHist.e0 zY) -> False) := by
  intro classified windowBound sameX sameY
  have pointClassified : RatHistoryClassifier (x (n + k)) (y (n + k)) :=
    classified k windowBound
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameX sameY pointClassified
  have readback : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (x (n + k)) ∧ PositiveUnaryDenominator (y (n + k)) :=
    RatHistoryClassifier_positive_denominators pointClassified
  have leftRows :
      UnaryHistory (x (n + k)) ∧ (hsame (x (n + k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (y (n + k)) ∧ (hsame (y (n + k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨displayed, readback.left, readback.right.left, readback.right.right,
    positives.left, positives.right, leftRows.left, rightRows.left, leftRows.right,
    rightRows.right,
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))⟩

end BEDC.Derived.RealUp
