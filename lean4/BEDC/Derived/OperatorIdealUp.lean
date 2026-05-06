import BEDC.FKernel.Unary

namespace BEDC.Derived.OperatorIdealUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

inductive OperatorIdealBoundedContextAction : BHist -> BHist -> Prop where
  | id {T : BHist} : OperatorIdealBoundedContextAction T T
  | left {A T U result : BHist} :
      UnaryHistory A -> OperatorIdealBoundedContextAction T U -> Cont A U result ->
        OperatorIdealBoundedContextAction T result
  | right {A T U result : BHist} :
      UnaryHistory A -> OperatorIdealBoundedContextAction T U -> Cont U A result ->
        OperatorIdealBoundedContextAction T result

inductive OperatorIdealTraceClassCarrier (T : BHist) : Prop where
  | mk (support : BHist) :
      UnaryHistory support -> Cont support BHist.Empty T -> OperatorIdealTraceClassCarrier T

theorem OperatorIdealTraceClass_finite_context_closure {T result : BHist} :
    OperatorIdealTraceClassCarrier T -> OperatorIdealBoundedContextAction T result ->
      OperatorIdealTraceClassCarrier result := by
  intro carrier action
  induction action with
  | id =>
      exact carrier
  | left leftUnary _step rel ih =>
      have carried := ih carrier
      cases carried with
      | mk support supportUnary visible =>
          cases visible
          simp only [append_empty_right] at rel
          exact
            OperatorIdealTraceClassCarrier.mk _
              (unary_cont_closed leftUnary supportUnary rel)
              (cont_right_unit _)
  | right rightUnary _step rel ih =>
      have carried := ih carrier
      cases carried with
      | mk support supportUnary visible =>
          cases visible
          simp only [append_empty_right] at rel
          exact
            OperatorIdealTraceClassCarrier.mk _
              (unary_cont_closed supportUnary rightUnary rel)
              (cont_right_unit _)

theorem OperatorIdealTraceClass_two_sided_absorption_row {A T left right : BHist} :
    UnaryHistory A -> OperatorIdealTraceClassCarrier T -> Cont A T left -> Cont T A right ->
      OperatorIdealTraceClassCarrier left ∧ OperatorIdealTraceClassCarrier right := by
  intro unaryA carrierT leftCont rightCont
  have leftAction : OperatorIdealBoundedContextAction T left :=
    OperatorIdealBoundedContextAction.left unaryA
      (OperatorIdealBoundedContextAction.id (T := T)) leftCont
  have rightAction : OperatorIdealBoundedContextAction T right :=
    OperatorIdealBoundedContextAction.right unaryA
      (OperatorIdealBoundedContextAction.id (T := T)) rightCont
  exact And.intro
    (OperatorIdealTraceClass_finite_context_closure carrierT leftAction)
    (OperatorIdealTraceClass_finite_context_closure carrierT rightAction)

end BEDC.Derived.OperatorIdealUp
