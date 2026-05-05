import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

def NetworkFlowUSum (a : BHist → BHist) : List BHist → BHist
  | [] => BHist.Empty
  | e :: xs => append (a e) (NetworkFlowUSum a xs)

theorem NetworkFlowUSum_unary_closed {xs : List BHist} {a : BHist → BHist} :
    (∀ {e : BHist}, List.Mem e xs → UnaryHistory (a e)) →
      UnaryHistory (NetworkFlowUSum a xs) := by
  intro unaryA
  induction xs with
  | nil =>
      exact unary_empty
  | cons e xs ih =>
      exact unary_append_closed (unaryA (List.Mem.head xs))
        (ih (by
          intro z memZ
          exact unaryA (List.Mem.tail e memZ)))

theorem NetworkFlowUSum_monotonicity {xs : List BHist} {a b : BHist → BHist} :
    (∀ {e : BHist}, List.Mem e xs → UnaryHistory (a e)) →
      (∀ {e : BHist}, List.Mem e xs → UnaryHistory (b e)) →
        (∀ {e : BHist}, List.Mem e xs → PreorderPrefixLE (a e) (b e)) →
          PreorderPrefixLE (NetworkFlowUSum a xs) (NetworkFlowUSum b xs) := by
  intro unaryA unaryB pointwise
  induction xs with
  | nil =>
      exact PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)
  | cons e xs ih =>
      have tailAUnary : UnaryHistory (NetworkFlowUSum a xs) :=
        NetworkFlowUSum_unary_closed (xs := xs) (a := a) (by
          intro z memZ
          exact unaryA (List.Mem.tail e memZ))
      have headStep : PreorderPrefixLE (a e) (b e) :=
        pointwise (List.Mem.head xs)
      have tailStep : PreorderPrefixLE (NetworkFlowUSum a xs) (NetworkFlowUSum b xs) :=
        ih
          (by
            intro z memZ
            exact unaryA (List.Mem.tail e memZ))
          (by
            intro z memZ
            exact unaryB (List.Mem.tail e memZ))
          (by
            intro z memZ
            exact pointwise (List.Mem.tail e memZ))
      exact PreorderPrefixLE_trans
        (PreorderPrefixLE_append_right_context tailAUnary headStep)
        (PreorderPrefixLE_append_left_context tailStep)

end BEDC.Derived.NetworkFlowUp
