import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

def NetworkFlowUSum : List BHist -> (BHist -> BHist) -> BHist
  | [], _ => BHist.Empty
  | e :: xs, a => append (a e) (NetworkFlowUSum xs a)

theorem NetworkFlowUSum_unary {xs : List BHist} {a : BHist -> BHist} :
    (forall e : BHist, List.Mem e xs -> UnaryHistory (a e)) ->
      UnaryHistory (NetworkFlowUSum xs a) := by
  intro unaryA
  induction xs with
  | nil =>
      exact unary_empty
  | cons e xs ih =>
      exact unary_append_closed (unaryA e (List.Mem.head xs))
        (ih (fun t mem => unaryA t (List.Mem.tail e mem)))

theorem NetworkFlowUSum_prefix_monotone {xs : List BHist} {a b : BHist -> BHist} :
    (forall e : BHist, List.Mem e xs -> UnaryHistory (a e)) ->
      (forall e : BHist, List.Mem e xs -> PreorderPrefixLE (a e) (b e)) ->
        PreorderPrefixLE (NetworkFlowUSum xs a) (NetworkFlowUSum xs b) := by
  intro unaryA pointwise
  induction xs with
  | nil =>
      exact PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)
  | cons e xs ih =>
      have tailUnary : UnaryHistory (NetworkFlowUSum xs a) :=
        NetworkFlowUSum_unary (fun t mem => unaryA t (List.Mem.tail e mem))
      have headStep :
          PreorderPrefixLE (append (a e) (NetworkFlowUSum xs a))
            (append (b e) (NetworkFlowUSum xs a)) :=
        PreorderPrefixLE_append_right_context tailUnary
          (pointwise e (List.Mem.head xs))
      have tailStep :
          PreorderPrefixLE (append (b e) (NetworkFlowUSum xs a))
            (append (b e) (NetworkFlowUSum xs b)) :=
        PreorderPrefixLE_append_left_context
          (ih (fun t mem => unaryA t (List.Mem.tail e mem))
            (fun t mem => pointwise t (List.Mem.tail e mem)))
      exact PreorderPrefixLE_trans headStep tailStep

theorem NetworkFlow_empty_backward_accounting_cut_flow_below_value {V B X : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE X V := by
  intro _backwardUnary backwardEmpty accounting
  cases backwardEmpty
  have sameXV : hsame X V := cont_deterministic accounting (cont_right_unit V)
  exact PreorderPrefixLE_of_hsame sameXV

end BEDC.Derived.NetworkFlowUp
