import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.Commutativity
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

def NetworkFlowUnaryFold (weight : BHist -> BHist) : List BHist -> BHist
  | [] => BHist.Empty
  | e :: es => append (weight e) (NetworkFlowUnaryFold weight es)

theorem NetworkFlowUnaryFold_unary {weight : BHist -> BHist}
    (weightUnary : forall {e : BHist}, UnaryHistory (weight e)) :
    forall xs : List BHist, UnaryHistory (NetworkFlowUnaryFold weight xs) := by
  intro xs
  induction xs with
  | nil =>
      exact unary_empty
  | cons e es ih =>
      exact unary_append_closed weightUnary ih

theorem NetworkFlowUnaryFold_pointwise_prefix_monotonicity {a b : BHist -> BHist}
    (aUnary : forall {e : BHist}, UnaryHistory (a e))
    (bUnary : forall {e : BHist}, UnaryHistory (b e))
    (pointwise : forall {e : BHist},
      exists tail : BHist, UnaryHistory tail ∧ Cont (a e) tail (b e)) :
    forall xs : List BHist,
      exists tail : BHist,
        UnaryHistory tail ∧ Cont (NetworkFlowUnaryFold a xs) tail (NetworkFlowUnaryFold b xs) := by
  intro xs
  induction xs with
  | nil =>
      have _targetUnary : UnaryHistory (NetworkFlowUnaryFold b []) :=
        NetworkFlowUnaryFold_unary bUnary []
      exact ⟨BHist.Empty, unary_empty, cont_right_unit BHist.Empty⟩
  | cons e es ih =>
      have _targetUnary : UnaryHistory (NetworkFlowUnaryFold b (e :: es)) :=
        NetworkFlowUnaryFold_unary bUnary (e :: es)
      cases pointwise (e := e) with
      | intro headTail headData =>
          cases headData with
          | intro headTailUnary headCont =>
              cases ih with
              | intro foldTail foldData =>
                  cases foldData with
                  | intro foldTailUnary foldCont =>
                      have foldAUnary : UnaryHistory (NetworkFlowUnaryFold a es) :=
                        NetworkFlowUnaryFold_unary aUnary es
                      have middleComm :
                          append headTail (NetworkFlowUnaryFold a es) =
                            append (NetworkFlowUnaryFold a es) headTail :=
                        unary_append_comm headTailUnary foldAUnary
                      exact
                        ⟨append headTail foldTail,
                          unary_append_closed headTailUnary foldTailUnary,
                          by
                            exact cont_intro
                              (calc
                                append (b e) (NetworkFlowUnaryFold b es)
                                    = append (append (a e) headTail)
                                        (NetworkFlowUnaryFold b es) :=
                                      congrArg
                                        (fun head => append head (NetworkFlowUnaryFold b es))
                                        headCont
                                _ = append (append (a e) headTail)
                                      (append (NetworkFlowUnaryFold a es) foldTail) :=
                                      congrArg (append (append (a e) headTail)) foldCont
                                _ = append (a e)
                                        (append headTail
                                          (append (NetworkFlowUnaryFold a es) foldTail)) :=
                                      append_assoc (a e) headTail
                                        (append (NetworkFlowUnaryFold a es) foldTail)
                                _ = append (a e)
                                      (append (append headTail (NetworkFlowUnaryFold a es))
                                        foldTail) :=
                                      congrArg (append (a e))
                                        (append_assoc headTail (NetworkFlowUnaryFold a es)
                                          foldTail).symm
                                _ = append (a e)
                                      (append (append (NetworkFlowUnaryFold a es) headTail)
                                        foldTail) :=
                                      congrArg
                                        (fun middle =>
                                          append (a e) (append middle foldTail))
                                        middleComm
                                _ = append (a e)
                                      (append (NetworkFlowUnaryFold a es)
                                        (append headTail foldTail)) :=
                                      congrArg (append (a e))
                                        (append_assoc (NetworkFlowUnaryFold a es) headTail
                                          foldTail)
                                _ = append (append (a e) (NetworkFlowUnaryFold a es))
                                      (append headTail foldTail) :=
                                      (append_assoc (a e) (NetworkFlowUnaryFold a es)
                                        (append headTail foldTail)).symm)⟩

theorem NetworkFlow_empty_backward_accounting_cut_flow_below_value {V B X : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE X V := by
  intro _backwardUnary backwardEmpty accounting
  cases backwardEmpty
  have sameXV : hsame X V := cont_deterministic accounting (cont_right_unit V)
  exact PreorderPrefixLE_of_hsame sameXV

theorem NetworkFlowUSum_monotone {xs : List BHist} {a b : BHist -> BHist} :
    (forall e : BHist, e ∈ xs -> UnaryHistory (a e)) ->
    (forall e : BHist, e ∈ xs -> UnaryHistory (b e)) ->
    (forall e : BHist, e ∈ xs -> PreorderPrefixLE (a e) (b e)) ->
      PreorderPrefixLE (NetworkFlowUSum a xs) (NetworkFlowUSum b xs) := by
  intro unaryA unaryB pointwise
  exact NetworkFlowUSum_monotonicity (xs := xs) (a := a) (b := b)
    (by
      intro e memE
      exact unaryA e memE)
    (by
      intro e memE
      exact unaryB e memE)
    (by
      intro e memE
      exact pointwise e memE)

theorem NetworkFlowEmptyBackwardAccounting_cut_flow_below_value {V B X : BHist} :
    Cont V B X -> hsame B BHist.Empty -> PreorderPrefixLE X V := by
  intro accounting backwardEmpty
  have transported : Cont V BHist.Empty X :=
    cont_hsame_transport (hsame_refl V) backwardEmpty (hsame_refl X) accounting
  have sameXV : hsame X V :=
    cont_right_unit_result transported
  exact PreorderPrefixLE_of_hsame sameXV

end BEDC.Derived.NetworkFlowUp
