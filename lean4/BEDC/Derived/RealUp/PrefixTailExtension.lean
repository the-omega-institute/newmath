import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamPrefixClassifier_tail_extension_with_unary_anchor {x y : Nat -> BHist} :
    forall n m : Nat, RealStreamPrefixClassifier x y n ->
      (forall k : Nat, k < m ->
        RatHistoryClassifier (x (n + Nat.succ k)) (y (n + Nat.succ k))) ->
          (forall i : Nat, UnaryHistory (x i)) ->
            RealStreamPrefixClassifier x y (n + m) ∧ UnaryHistory (x (n + m)) := by
  intro n m
  induction m with
  | zero =>
      intro basePrefix _tail unary
      constructor
      · simpa only [Nat.add_zero] using basePrefix
      · simpa only [Nat.add_zero] using unary n
  | succ m ih =>
      intro basePrefix tail unary
      have restrictedTail :
          forall k : Nat, k < m ->
            RatHistoryClassifier (x (n + Nat.succ k)) (y (n + Nat.succ k)) := by
        intro k kLt
        exact tail k (Nat.lt_trans kLt (Nat.lt_succ_self m))
      have prefixAtTail := ih basePrefix restrictedTail unary
      have finalEndpoint :
          RatHistoryClassifier (x (n + Nat.succ m)) (y (n + Nat.succ m)) :=
        tail m (Nat.lt_succ_self m)
      constructor
      · simp only [Nat.add_succ]
        exact And.intro prefixAtTail.left (by
          simpa only [Nat.add_succ] using finalEndpoint)
      · simp only [Nat.add_succ]
        exact unary (Nat.succ (n + m))

end BEDC.Derived.RealUp
