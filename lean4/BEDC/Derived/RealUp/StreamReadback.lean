import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_selected_e1_pair_readback {x y : Nat -> BHist} {n : Nat}
    {a b : BHist} :
    RealStreamClassifier x y -> hsame (x n) (BHist.e1 a) ->
      hsame (y n) (BHist.e1 b) -> UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified sameLeft sameRight
  have pointClassified : RatHistoryClassifier (x n) (y n) := classified n
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight pointClassified
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RealStreamClassifier_transported_selected_e1_pair_readback
    {x x' y y' : Nat -> BHist} {n : Nat} {a b : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) -> RealStreamClassifier x y ->
        hsame (x' n) (BHist.e1 a) -> hsame (y' n) (BHist.e1 b) ->
          UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro sameX sameY classified sameLeft sameRight
  have pointClassified : RatHistoryClassifier (x n) (y n) := classified n
  have transported : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) pointClassified
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight transported
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

end BEDC.Derived.RealUp
