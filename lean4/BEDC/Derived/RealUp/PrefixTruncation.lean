import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealStreamPrefixClassifier_truncated_e1_pair_readback {x y : Nat -> BHist} :
    forall {n m : Nat} {leftTail rightTail : BHist},
      RealStreamPrefixClassifier x y (m + n) ->
        hsame (x n) (BHist.e1 leftTail) ->
          hsame (y n) (BHist.e1 rightTail) ->
            UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro n m
  induction m with
  | zero =>
      intro leftTail rightTail classified sameLeft sameRight
      simp only [Nat.zero_add] at classified
      exact RealStreamPrefixClassifier_e1_pair_readback classified sameLeft sameRight
  | succ m ih =>
      intro leftTail rightTail classified sameLeft sameRight
      have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
        simp only [Nat.succ_add] at classified
        exact classified
      exact ih stepClassified.left sameLeft sameRight

end BEDC.Derived.RealUp
