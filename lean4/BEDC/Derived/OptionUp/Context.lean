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

end BEDC.Derived.OptionUp
