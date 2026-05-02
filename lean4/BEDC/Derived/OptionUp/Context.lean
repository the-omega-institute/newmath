import BEDC.Derived.OptionUp.PrefixClosure
import BEDC.Derived.OptionUp.SuffixClosure

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem OptionHistoryClassifier_unary_two_sided_context_iff {p q h k : BHist} :
    UnaryHistory p -> UnaryHistory q ->
      (OptionHistoryClassifier UnaryHistory h k ↔
        OptionHistoryClassifier UnaryHistory (append p (append h q))
          (append p (append k q))) := by
  intro pCarrier qCarrier
  constructor
  · intro classifier
    exact
      OptionHistoryClassifier_unary_prefix_closed pCarrier
        (OptionHistoryClassifier_unary_suffix_closed qCarrier classifier)
  · intro contextual
    have sourceCarrier : UnaryHistory h := by
      cases contextual.left with
      | inl emptyCase =>
          have tailEmpty := (append_eq_empty_iff.mp emptyCase).right
          have coreEmpty := (append_eq_empty_iff.mp tailEmpty).left
          cases coreEmpty
          exact unary_empty
      | inr unaryContext =>
          exact unary_append_left_factor (unary_append_right_factor unaryContext)
    have targetCarrier : UnaryHistory k := by
      cases contextual.right.left with
      | inl emptyCase =>
          have tailEmpty := (append_eq_empty_iff.mp emptyCase).right
          have coreEmpty := (append_eq_empty_iff.mp tailEmpty).left
          cases coreEmpty
          exact unary_empty
      | inr unaryContext =>
          exact unary_append_left_factor (unary_append_right_factor unaryContext)
    have sameTails : hsame (append h q) (append k q) :=
      append_left_cancel contextual.right.right
    have sameCore : hsame h k :=
      append_right_cancel (k := q) sameTails
    exact And.intro (Or.inr sourceCarrier) (And.intro (Or.inr targetCarrier) sameCore)

theorem OptionHistoryCarrier_unary_two_sided_context_iff {p q h : BHist} :
    UnaryHistory p -> UnaryHistory q ->
      (OptionHistoryCarrier UnaryHistory h ↔
        OptionHistoryCarrier UnaryHistory (append p (append h q))) := by
  intro pCarrier qCarrier
  constructor
  · intro carrier
    exact
      OptionHistoryCarrier_unary_prefix_closed pCarrier
        (OptionHistoryCarrier_unary_suffix_closed qCarrier carrier)
  · intro contextual
    cases contextual with
    | inl emptyCase =>
        have tailEmpty := (append_eq_empty_iff.mp emptyCase).right
        have coreEmpty := (append_eq_empty_iff.mp tailEmpty).left
        cases coreEmpty
        exact Or.inl (hsame_refl BHist.Empty)
    | inr unaryContext =>
        exact Or.inr (unary_append_left_factor (unary_append_right_factor unaryContext))

theorem OptionHistoryClassifier_unary_context_composition_iff {p q r s h k : BHist} :
    UnaryHistory p -> UnaryHistory q -> UnaryHistory r -> UnaryHistory s ->
      (OptionHistoryClassifier UnaryHistory h k ↔
        OptionHistoryClassifier UnaryHistory
          (append p (append (append r (append h s)) q))
          (append (append p r) (append k (append s q)))) := by
  intro pCarrier qCarrier rCarrier sCarrier
  let L := append p r
  let R := append s q
  have lCarrier : UnaryHistory L := unary_append_closed pCarrier rCarrier
  have rCarrier' : UnaryHistory R := unary_append_closed sCarrier qCarrier
  have sourceSame : hsame (append p (append (append r (append h s)) q))
      (append L (append h R)) := by
    have sourceSameByRewrite : append p (append (append r (append h s)) q) =
        append L (append h R) := by
      show append p (append (append r (append h s)) q) = append L (append h R)
      rw [append_assoc r (append h s) q, append_assoc h s q,
          ← append_assoc p r (append h (append s q))]
    have sourceSameByComposition : append p (append (append r (append h s)) q) =
        append L (append h R) := by
      change append p (append (append r (append h s)) q) =
        append (append p r) (append h (append s q))
      exact
        (congrArg (append p)
          ((append_assoc r (append h s) q).trans
            (congrArg (append r) (append_assoc h s q)))).trans
          (append_assoc p r (append h (append s q))).symm
    exact sourceSameByRewrite
  have targetSame : hsame (append (append p r) (append k (append s q)))
      (append L (append k R)) := by
    rfl
  constructor
  · intro classifier
    have contextual := (OptionHistoryClassifier_unary_two_sided_context_iff (p := L) (q := R)
      (h := h) (k := k) lCarrier rCarrier').mp classifier
    exact
      OptionHistoryClassifier_hsame_transport (hsame_symm sourceSame) (hsame_symm targetSame)
        contextual
  · intro contextual
    have normalized := OptionHistoryClassifier_hsame_transport sourceSame targetSame contextual
    exact (OptionHistoryClassifier_unary_two_sided_context_iff (p := L) (q := R)
      (h := h) (k := k) lCarrier rCarrier').mpr normalized

end BEDC.Derived.OptionUp
