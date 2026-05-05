import BEDC.FKernel.Bundle
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle
open BEDC.Derived.PreorderUp

def NetworkFlowUSum (a : BHist -> BHist) : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons e xs => append (a e) (NetworkFlowUSum a xs)

def NetworkFlowUSumSpineUnary (a : BHist -> BHist) : ProbeBundle BHist -> Prop
  | ProbeBundle.Bnil => UnaryHistory BHist.Empty
  | ProbeBundle.Bcons e xs => UnaryHistory (a e) ∧ NetworkFlowUSumSpineUnary a xs

theorem NetworkFlow_unary_finite_fold_monotonicity {a b : BHist -> BHist}
    {xs : ProbeBundle BHist} :
    NetworkFlowUSumSpineUnary a xs ->
      NetworkFlowUSumSpineUnary b xs ->
        (forall e : BHist, InBundle e xs -> PreorderPrefixLE (a e) (b e)) ->
          PreorderPrefixLE (NetworkFlowUSum a xs) (NetworkFlowUSum b xs) := by
  have foldUnary :
      forall {f : BHist -> BHist} {bundle : ProbeBundle BHist},
        NetworkFlowUSumSpineUnary f bundle -> UnaryHistory (NetworkFlowUSum f bundle) := by
    intro f bundle spine
    induction bundle with
    | Bnil =>
        exact unary_empty
    | Bcons e tail ih =>
        exact unary_append_closed spine.left (ih spine.right)
  intro spineA spineB pointwise
  induction xs with
  | Bnil =>
      exact PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)
  | Bcons e tail ih =>
      have headLE : PreorderPrefixLE (a e) (b e) :=
        pointwise e (Or.inl rfl)
      have tailPointwise :
          forall q : BHist, InBundle q tail -> PreorderPrefixLE (a q) (b q) := by
        intro q member
        exact pointwise q (Or.inr member)
      have tailLE :
          PreorderPrefixLE (NetworkFlowUSum a tail) (NetworkFlowUSum b tail) :=
        ih spineA.right spineB.right tailPointwise
      have rightContext :
          PreorderPrefixLE (append (a e) (NetworkFlowUSum a tail))
            (append (b e) (NetworkFlowUSum a tail)) :=
        PreorderPrefixLE_append_right_context (foldUnary spineA.right) headLE
      have leftContext :
          PreorderPrefixLE (append (b e) (NetworkFlowUSum a tail))
            (append (b e) (NetworkFlowUSum b tail)) :=
        PreorderPrefixLE_append_left_context tailLE
      exact PreorderPrefixLE_trans rightContext leftContext

theorem NetworkFlow_empty_backward_accounting_cut_flow_below_value {V B X : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE X V := by
  intro _backwardUnary backwardEmpty accounting
  cases backwardEmpty
  have sameXV : hsame X V := cont_deterministic accounting (cont_right_unit V)
  exact PreorderPrefixLE_of_hsame sameXV

end BEDC.Derived.NetworkFlowUp
