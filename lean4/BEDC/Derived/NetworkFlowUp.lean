import BEDC.FKernel.Unary.Commutativity
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

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

end BEDC.Derived.NetworkFlowUp
