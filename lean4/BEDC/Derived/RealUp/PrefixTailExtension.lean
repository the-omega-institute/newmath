import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem RealStreamPrefixClassifier_tail_endpoint_context_projection
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {n m : Nat} :
    RealStreamPrefixClassifier x y n ->
      (forall k : Nat, k < m ->
        RatHistoryClassifier (x (n + Nat.succ k)) (y (n + Nat.succ k))) ->
        (forall i : Nat, UnaryHistory (x i)) -> UnaryHistory (prefX (n + m)) ->
          UnaryHistory (tailX (n + m)) -> hsame (prefX (n + m)) (prefY (n + m)) ->
            hsame (tailX (n + m)) (tailY (n + m)) ->
              Cont (prefX (n + m)) (x (n + m)) (midX (n + m)) ->
                Cont (midX (n + m)) (tailX (n + m)) (outX (n + m)) ->
                  Cont (prefY (n + m)) (y (n + m)) (midY (n + m)) ->
                    Cont (midY (n + m)) (tailY (n + m)) (outY (n + m)) ->
                      RatHistoryClassifier (outX (n + m)) (outY (n + m)) := by
  intro basePrefix tail unary prefUnary tailUnary samePref sameTail prefXCont outXCont
  intro prefYCont outYCont
  have extended :=
    RealStreamPrefixClassifier_tail_extension_with_unary_anchor (x := x) (y := y) n m basePrefix
      tail unary
  have endpoint : RatHistoryClassifier (x (n + m)) (y (n + m)) :=
    RealStreamPrefixClassifier_endpoint (n + m) extended.left
  have contextClassified :
      RatHistoryClassifier (append (prefX (n + m)) (append (x (n + m)) (tailX (n + m))))
        (append (prefY (n + m)) (append (y (n + m)) (tailY (n + m)))) :=
    RatHistoryClassifier_unary_denominator_context_closed endpoint prefUnary samePref tailUnary
      sameTail
  have sameOutX :
      hsame (append (prefX (n + m)) (append (x (n + m)) (tailX (n + m))))
        (outX (n + m)) := by
    exact (append_assoc (prefX (n + m)) (x (n + m)) (tailX (n + m))).symm.trans
      ((congrArg (fun h : BHist => append h (tailX (n + m))) prefXCont.symm).trans
        outXCont.symm)
  have sameOutY :
      hsame (append (prefY (n + m)) (append (y (n + m)) (tailY (n + m))))
        (outY (n + m)) := by
    exact (append_assoc (prefY (n + m)) (y (n + m)) (tailY (n + m))).symm.trans
      ((congrArg (fun h : BHist => append h (tailY (n + m))) prefYCont.symm).trans
        outYCont.symm)
  exact RatHistoryClassifier_hsame_transport sameOutX sameOutY contextClassified

end BEDC.Derived.RealUp
