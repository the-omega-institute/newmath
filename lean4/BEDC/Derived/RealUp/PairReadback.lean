import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamPrefixClassifier_hsame_e1_pair_readback {x x' y y' : Nat -> BHist}
    (sameX : forall n : Nat, hsame (x n) (x' n))
    (sameY : forall n : Nat, hsame (y n) (y' n)) {n : Nat} {a b : BHist} :
    RealStreamPrefixClassifier x y n -> hsame (x' n) (BHist.e1 a) ->
      hsame (y' n) (BHist.e1 b) -> UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro hPrefix sameLeft sameRight
  have transported : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  exact RealStreamPrefixClassifier_e1_pair_readback transported sameLeft sameRight

theorem RealStreamClassifier_hsame_e1_pair_readback {x x' y y' : Nat -> BHist}
    (sameX : forall n : Nat, hsame (x n) (x' n))
    (sameY : forall n : Nat, hsame (y n) (y' n)) {n : Nat} {a b : BHist} :
    RealStreamClassifier x y -> hsame (x' n) (BHist.e1 a) ->
      hsame (y' n) (BHist.e1 b) -> UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified sameLeft sameRight
  have atIndex : RatHistoryClassifier (x n) (y n) := classified n
  have transported : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) atIndex
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight transported
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

end BEDC.Derived.RealUp
