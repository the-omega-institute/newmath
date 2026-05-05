import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

theorem NetworkFlow_empty_backward_accounting_cut_flow_below_value {V B X : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE X V := by
  intro _backwardUnary backwardEmpty accounting
  cases backwardEmpty
  have sameXV : hsame X V := cont_deterministic accounting (cont_right_unit V)
  exact PreorderPrefixLE_of_hsame sameXV

def NetworkFlowUSum (xs : List BHist) (a : BHist -> BHist) : BHist :=
  match xs with
  | [] => BHist.Empty
  | e :: rest => append (a e) (NetworkFlowUSum rest a)

theorem NetworkFlowUSum_unary {xs : List BHist} {a : BHist -> BHist} :
    (forall e : BHist, e ∈ xs -> UnaryHistory (a e)) ->
      UnaryHistory (NetworkFlowUSum xs a) := by
  intro unaryA
  induction xs with
  | nil =>
      exact unary_empty
  | cons e rest ih =>
      exact unary_append_closed (unaryA e (List.Mem.head rest)) (ih (by
        intro x memRest
        exact unaryA x (List.Mem.tail e memRest)))

theorem NetworkFlowUSum_monotone {xs : List BHist} {a b : BHist -> BHist} :
    (forall e : BHist, e ∈ xs -> UnaryHistory (a e)) ->
    (forall e : BHist, e ∈ xs -> UnaryHistory (b e)) ->
    (forall e : BHist, e ∈ xs -> PreorderPrefixLE (a e) (b e)) ->
      PreorderPrefixLE (NetworkFlowUSum xs a) (NetworkFlowUSum xs b) := by
  intro unaryA unaryB pointwise
  induction xs with
  | nil =>
      exact PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)
  | cons e rest ih =>
      have tailUnaryA : UnaryHistory (NetworkFlowUSum rest a) :=
        NetworkFlowUSum_unary (xs := rest) (a := a) (by
          intro x memRest
          exact unaryA x (List.Mem.tail e memRest))
      have headStep : PreorderPrefixLE (a e) (b e) :=
        pointwise e (List.Mem.head rest)
      have tailStep :
          PreorderPrefixLE (NetworkFlowUSum rest a) (NetworkFlowUSum rest b) :=
        ih
          (by
            intro x memRest
            exact unaryA x (List.Mem.tail e memRest))
          (by
            intro x memRest
            exact unaryB x (List.Mem.tail e memRest))
          (by
            intro x memRest
            exact pointwise x (List.Mem.tail e memRest))
      exact PreorderPrefixLE_trans
        (PreorderPrefixLE_append_right_context tailUnaryA headStep)
        (PreorderPrefixLE_append_left_context tailStep)

end BEDC.Derived.NetworkFlowUp
