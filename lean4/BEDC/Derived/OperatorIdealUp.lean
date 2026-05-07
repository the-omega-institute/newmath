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

theorem OperatorIdealTraceClass_support_readback {T : BHist} :
    OperatorIdealTraceClassCarrier T -> exists support : BHist, UnaryHistory support ∧
      Cont support BHist.Empty T := by
  intro carrier
  cases carrier with
  | mk support supportUnary supportVisible =>
      exact ⟨support, supportUnary, supportVisible⟩

theorem OperatorIdealTraceClass_root_carrier_classifier_threshold {T : BHist} :
    OperatorIdealTraceClassCarrier T -> exists support : BHist, UnaryHistory support ∧
      Cont support BHist.Empty T ∧ hsame T support := by
  intro carrier
  cases carrier with
  | mk support supportUnary supportVisible =>
      have endpointSame : hsame T support :=
        cont_deterministic supportVisible (cont_right_unit support)
      exact ⟨support, supportUnary, supportVisible, endpointSame⟩

theorem OperatorIdealTraceClass_downstream_boundary_readback {T : BHist} :
    OperatorIdealTraceClassCarrier T ->
      UnaryHistory T ∧
        (exists support : BHist, UnaryHistory support ∧
          Cont support BHist.Empty T ∧ hsame T support) := by
  intro carrier
  cases carrier with
  | mk support supportUnary supportVisible =>
      have endpointSame : hsame T support :=
        cont_deterministic supportVisible (cont_right_unit support)
      exact And.intro
        (unary_transport supportUnary (hsame_symm endpointSame))
        (Exists.intro support
          (And.intro supportUnary (And.intro supportVisible endpointSame)))

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

theorem OperatorIdealTraceClass_scalar_closure {a T result : BHist} :
    UnaryHistory a -> OperatorIdealTraceClassCarrier T -> Cont a T result ->
      OperatorIdealTraceClassCarrier result ∧ OperatorIdealBoundedContextAction T result := by
  intro unaryA carrierT scalarCont
  have scalarAction : OperatorIdealBoundedContextAction T result :=
    OperatorIdealBoundedContextAction.left unaryA
      (OperatorIdealBoundedContextAction.id (T := T)) scalarCont
  exact And.intro
    (OperatorIdealTraceClass_finite_context_closure carrierT scalarAction)
    scalarAction

theorem OperatorIdealBoundedContextAction_row_separation {T result : BHist} :
    OperatorIdealBoundedContextAction T result -> hsame result T ∨
      exists A : BHist, exists U : BHist,
        UnaryHistory A ∧ OperatorIdealBoundedContextAction T U ∧
          (Cont A U result ∨ Cont U A result) := by
  intro action
  induction action with
  | id =>
      exact Or.inl (hsame_refl _)
  | left unaryA step rel _ =>
      exact Or.inr
        (Exists.intro _
          (Exists.intro _
            (And.intro unaryA (And.intro step (Or.inl rel)))))
  | right unaryA step rel _ =>
      exact Or.inr
        (Exists.intro _
          (Exists.intro _
            (And.intro unaryA (And.intro step (Or.inr rel)))))

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

theorem OperatorIdealBoundedContextAction_consumer_context_exhaustion {T result : BHist} :
    OperatorIdealTraceClassCarrier T -> OperatorIdealBoundedContextAction T result ->
      OperatorIdealTraceClassCarrier result ∧
        (hsame result T ∨
          exists A : BHist, exists U : BHist,
            UnaryHistory A ∧ OperatorIdealBoundedContextAction T U ∧
              (Cont A U result ∨ Cont U A result)) := by
  intro carrier action
  constructor
  · exact OperatorIdealTraceClass_finite_context_closure carrier action
  · exact OperatorIdealBoundedContextAction_row_separation action

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

theorem OperatorIdealTraceClass_root_ideal_absorption_threshold
    {a A T S sum neg scalar left right : BHist} :
    UnaryHistory a -> UnaryHistory A -> OperatorIdealTraceClassCarrier T ->
      OperatorIdealTraceClassCarrier S -> Cont T S sum -> Cont BHist.Empty T neg ->
        Cont a T scalar -> Cont A T left -> Cont T A right ->
          OperatorIdealTraceClassCarrier BHist.Empty ∧
            OperatorIdealTraceClassCarrier sum ∧
              OperatorIdealTraceClassCarrier neg ∧
                OperatorIdealTraceClassCarrier scalar ∧
                  OperatorIdealTraceClassCarrier left ∧
                    OperatorIdealTraceClassCarrier right := by
  intro unaryA0 unaryA carrierT carrierS sumCont negCont scalarCont leftCont rightCont
  have additiveRows :=
    OperatorIdealTraceClass_additive_closure_row (T := T) (S := S) (sum := sum) (neg := neg)
  have scalarRows :=
    OperatorIdealTraceClass_scalar_closure unaryA0 carrierT scalarCont
  have absorptionRows :=
    OperatorIdealTraceClass_two_sided_absorption_row unaryA carrierT leftCont rightCont
  exact And.intro additiveRows.left
    (And.intro (additiveRows.right.left carrierT carrierS sumCont)
      (And.intro (additiveRows.right.right carrierT negCont)
        (And.intro scalarRows.left
          (And.intro absorptionRows.left absorptionRows.right))))

theorem OperatorIdealTraceClass_consumer_spine_coverage {T S sum neg A left right : BHist} :
    OperatorIdealTraceClassCarrier T -> OperatorIdealTraceClassCarrier S -> UnaryHistory A ->
      Cont T S sum -> Cont BHist.Empty T neg -> Cont A T left -> Cont T A right ->
        OperatorIdealTraceClassCarrier sum ∧ OperatorIdealTraceClassCarrier neg ∧
          OperatorIdealTraceClassCarrier left ∧ OperatorIdealTraceClassCarrier right := by
  intro carrierT carrierS unaryA sumCont negCont leftCont rightCont
  have additiveRows :=
    OperatorIdealTraceClass_additive_closure_row (T := T) (S := S) (sum := sum) (neg := neg)
  have sumCarrier : OperatorIdealTraceClassCarrier sum :=
    additiveRows.right.left carrierT carrierS sumCont
  have negCarrier : OperatorIdealTraceClassCarrier neg :=
    additiveRows.right.right carrierT negCont
  have absorptionRows :=
    OperatorIdealTraceClass_two_sided_absorption_row unaryA carrierT leftCont rightCont
  exact And.intro sumCarrier
    (And.intro negCarrier
      (And.intro absorptionRows.left absorptionRows.right))

theorem OperatorIdealTraceClass_consumer_exhaustion
    {T S sum neg A left right result : BHist} :
    OperatorIdealTraceClassCarrier T -> OperatorIdealTraceClassCarrier S -> UnaryHistory A ->
      Cont T S sum -> Cont BHist.Empty T neg -> Cont A T left -> Cont T A right ->
        OperatorIdealBoundedContextAction T result ->
          OperatorIdealTraceClassCarrier sum ∧ OperatorIdealTraceClassCarrier neg ∧
            OperatorIdealTraceClassCarrier left ∧ OperatorIdealTraceClassCarrier right ∧
              OperatorIdealTraceClassCarrier result := by
  intro carrierT carrierS unaryA sumCont negCont leftCont rightCont action
  have consumerRows :=
    OperatorIdealTraceClass_consumer_spine_coverage carrierT carrierS unaryA sumCont
      negCont leftCont rightCont
  have resultCarrier : OperatorIdealTraceClassCarrier result :=
    OperatorIdealTraceClass_finite_context_closure carrierT action
  exact And.intro consumerRows.left
    (And.intro consumerRows.right.left
      (And.intro consumerRows.right.right.left
        (And.intro consumerRows.right.right.right resultCarrier)))

end BEDC.Derived.OperatorIdealUp
