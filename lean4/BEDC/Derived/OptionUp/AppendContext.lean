import BEDC.Derived.OptionUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem OptionHistoryCarrier_unary_append_context_iff {p q h : BHist} :
    UnaryHistory p -> UnaryHistory q ->
      (OptionHistoryCarrier UnaryHistory (append p (append h q)) ↔
        OptionHistoryCarrier UnaryHistory h) := by
  intro pUnary qUnary
  constructor
  · intro carrierContext
    cases carrierContext with
    | inl emptyContext =>
        have emptyParts := append_eq_empty_iff.mp emptyContext
        have middleParts := append_eq_empty_iff.mp emptyParts.right
        cases middleParts.left
        exact Or.inl (hsame_refl BHist.Empty)
    | inr unaryContext =>
        exact Or.inr ((unary_append_context_middle_iff pUnary qUnary).mp unaryContext)
  · intro carrier
    cases carrier with
    | inl emptyH =>
        cases emptyH
        exact Or.inr (unary_append_closed pUnary (unary_append_closed unary_empty qUnary))
    | inr unaryH =>
        exact Or.inr ((unary_append_context_middle_iff pUnary qUnary).mpr unaryH)

theorem OptionHistoryClassifier_unary_append_context_iff {p q h k : BHist} :
    UnaryHistory p -> UnaryHistory q ->
      (OptionHistoryClassifier UnaryHistory h k ↔
        OptionHistoryClassifier UnaryHistory (append p (append h q))
          (append p (append k q))) := by
  intro pUnary qUnary
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            constructor
            · exact (OptionHistoryCarrier_unary_append_context_iff pUnary qUnary).mpr carrierH
            · constructor
              · exact (OptionHistoryCarrier_unary_append_context_iff pUnary qUnary).mpr carrierK
              · cases sameHK
                exact hsame_refl (append p (append h q))
  · intro contextual
    cases contextual with
    | intro carrierContextH rest =>
        cases rest with
        | intro carrierContextK sameContext =>
            have carrierH :=
              (OptionHistoryCarrier_unary_append_context_iff pUnary qUnary).mp carrierContextH
            have carrierK :=
              (OptionHistoryCarrier_unary_append_context_iff pUnary qUnary).mp carrierContextK
            have sameMiddle : hsame (append h q) (append k q) := by
              exact append_left_cancel (h := p) sameContext
            have sameHK : hsame h k := by
              exact append_right_cancel (k := q) sameMiddle
            exact And.intro carrierH (And.intro carrierK sameHK)

end BEDC.Derived.OptionUp
