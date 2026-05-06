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

theorem OperatorIdealTraceClass_binary_linear_combination_closure
    {a b T S aT bS result : BHist} :
    UnaryHistory a -> UnaryHistory b -> OperatorIdealTraceClassCarrier T ->
      OperatorIdealTraceClassCarrier S -> Cont a T aT -> Cont b S bS ->
        Cont aT bS result -> OperatorIdealTraceClassCarrier result := by
  intro unaryA unaryB carrierT carrierS scalarA scalarB addScalars
  cases carrierT with
  | mk supportT supportUnaryT supportVisibleT =>
      cases carrierS with
      | mk supportS supportUnaryS supportVisibleS =>
          have supportTClass : hsame T supportT :=
            cont_deterministic supportVisibleT (cont_right_unit supportT)
          cases supportTClass
          have scalarUnaryA : UnaryHistory aT :=
            unary_cont_closed unaryA supportUnaryT scalarA
          have supportSClass : hsame S supportS :=
            cont_deterministic supportVisibleS (cont_right_unit supportS)
          cases supportSClass
          have scalarUnaryB : UnaryHistory bS :=
            unary_cont_closed unaryB supportUnaryS scalarB
          exact
            OperatorIdealTraceClassCarrier.mk _
              (unary_cont_closed scalarUnaryA scalarUnaryB addScalars)
              (cont_right_unit _)

theorem OperatorIdealTraceClass_additive_closure_row {T S sum neg : BHist} :
    OperatorIdealTraceClassCarrier BHist.Empty ∧
      (OperatorIdealTraceClassCarrier T -> OperatorIdealTraceClassCarrier S ->
        Cont T S sum -> OperatorIdealTraceClassCarrier sum) ∧
      (OperatorIdealTraceClassCarrier T -> Cont BHist.Empty T neg ->
        OperatorIdealTraceClassCarrier neg) := by
  constructor
  · exact OperatorIdealTraceClassCarrier.mk BHist.Empty unary_empty (cont_right_unit BHist.Empty)
  · constructor
    · intro carrierT carrierS sumRel
      cases carrierT with
      | mk supportT supportUnaryT supportVisibleT =>
          cases carrierS with
          | mk supportS supportUnaryS supportVisibleS =>
              have sameT : hsame T supportT :=
                cont_deterministic supportVisibleT (cont_right_unit supportT)
              cases sameT
              have sameS : hsame S supportS :=
                cont_deterministic supportVisibleS (cont_right_unit supportS)
              cases sameS
              exact OperatorIdealTraceClassCarrier.mk sum
                (unary_cont_closed supportUnaryT supportUnaryS sumRel)
                (cont_right_unit sum)
    · intro carrierT negRel
      cases carrierT with
      | mk supportT supportUnaryT supportVisibleT =>
          have sameT : hsame T supportT :=
            cont_deterministic supportVisibleT (cont_right_unit supportT)
          cases sameT
          exact OperatorIdealTraceClassCarrier.mk neg
            (unary_cont_closed unary_empty supportUnaryT negRel)
            (cont_right_unit neg)

end BEDC.Derived.OperatorIdealUp
