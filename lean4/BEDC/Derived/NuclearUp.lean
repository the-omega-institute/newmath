import BEDC.Derived.BanachUp
import BEDC.Derived.MetricUp
import BEDC.Derived.OperatorIdealUp

namespace BEDC.Derived.NuclearUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.MetricUp
open BEDC.Derived.OperatorIdealUp

theorem NuclearCarrier_obligation
    {banachSource banachTarget compactRow rankLedger endpoint : BHist} :
    BanachSingletonCarrier banachSource -> BanachSingletonCarrier banachTarget ->
      OperatorIdealTraceClassCarrier compactRow -> UnaryHistory rankLedger ->
        Cont (append banachSource banachTarget) compactRow endpoint ->
          UnaryHistory endpoint ∧ UnaryHistory compactRow ∧ UnaryHistory rankLedger := by
  intro sourceCarrier targetCarrier compactCarrier rankUnary endpointCont
  have sourceUnary : UnaryHistory banachSource :=
    unary_transport unary_empty (hsame_symm sourceCarrier.left)
  have targetUnary : UnaryHistory banachTarget :=
    unary_transport unary_empty (hsame_symm targetCarrier.left)
  have sourceTargetUnary : UnaryHistory (append banachSource banachTarget) :=
    unary_cont_closed sourceUnary targetUnary (cont_intro rfl)
  have compactUnary : UnaryHistory compactRow :=
    (OperatorIdealTraceClass_downstream_boundary_readback compactCarrier).left
  exact And.intro
    (unary_cont_closed sourceTargetUnary compactUnary endpointCont)
    (And.intro compactUnary rankUnary)

theorem NuclearCompactPrefixCarrier_banach_operator_rows
    {source target operator prefixHist : BHist} :
    BanachSingletonCarrier source -> BanachSingletonCarrier target ->
      OperatorIdealTraceClassCarrier operator -> Cont source operator prefixHist ->
        exists support : BHist,
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
            UnaryHistory prefixHist ∧ UnaryHistory support ∧
              Cont support BHist.Empty operator ∧ hsame operator support ∧
                MetricDistanceWitness source BHist.Empty BHist.Empty ∧
                  MetricDistanceWitness target BHist.Empty BHist.Empty ∧
                    Cont source operator prefixHist := by
  intro sourceCarrier targetCarrier operatorCarrier prefixCont
  have operatorRows :=
    OperatorIdealTraceClass_downstream_boundary_readback operatorCarrier
  cases operatorRows.right with
  | intro support supportRows =>
      have sourceUnary : UnaryHistory source :=
        unary_transport unary_empty (hsame_symm sourceCarrier.left)
      have targetUnary : UnaryHistory target :=
        unary_transport unary_empty (hsame_symm targetCarrier.left)
      have prefixUnary : UnaryHistory prefixHist :=
        unary_cont_closed sourceUnary operatorRows.left prefixCont
      exact Exists.intro support
        (And.intro sourceUnary
          (And.intro targetUnary
            (And.intro operatorRows.left
              (And.intro prefixUnary
                (And.intro supportRows.left
                  (And.intro supportRows.right.left
                    (And.intro supportRows.right.right
                      (And.intro sourceCarrier.right
                        (And.intro targetCarrier.right prefixCont)))))))))

def NuclearRankOnePrefixLedger
    (index coefficient vector partialSum tail : BHist) : Prop :=
  UnaryHistory index ∧ UnaryHistory coefficient ∧ UnaryHistory vector ∧
    Cont coefficient vector partialSum ∧ Cont index partialSum tail

theorem NuclearRankOnePrefixLedger_tail_readback
    {index coefficient vector partialSum tail : BHist} :
    NuclearRankOnePrefixLedger index coefficient vector partialSum tail ->
      UnaryHistory partialSum ∧ UnaryHistory tail ∧
        Cont coefficient vector partialSum ∧ Cont index partialSum tail := by
  intro ledger
  have partialUnary : UnaryHistory partialSum :=
    unary_cont_closed ledger.right.left ledger.right.right.left ledger.right.right.right.left
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed ledger.left partialUnary ledger.right.right.right.right
  exact And.intro partialUnary
    (And.intro tailUnary
      (And.intro ledger.right.right.right.left ledger.right.right.right.right))

theorem NuclearCompactOperator_banach_transport_surface
    {source source' target target' compactRow transportedEndpoint : BHist} :
    BanachSingletonCarrier source -> BanachSingletonCarrier target ->
      OperatorIdealTraceClassCarrier compactRow -> hsame source source' -> hsame target target' ->
        Cont (append source' target') compactRow transportedEndpoint ->
          UnaryHistory transportedEndpoint ∧ OperatorIdealTraceClassCarrier compactRow ∧
            hsame transportedEndpoint (append (append source target) compactRow) := by
  intro sourceCarrier targetCarrier compactCarrier sameSource sameTarget endpointCont
  have sourceUnary : UnaryHistory source :=
    unary_transport unary_empty (hsame_symm sourceCarrier.left)
  have targetUnary : UnaryHistory target :=
    unary_transport unary_empty (hsame_symm targetCarrier.left)
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have targetUnary' : UnaryHistory target' := unary_transport targetUnary sameTarget
  have sourceTargetUnary : UnaryHistory (append source' target') :=
    unary_cont_closed sourceUnary' targetUnary' (cont_intro rfl)
  have compactUnary : UnaryHistory compactRow :=
    (OperatorIdealTraceClass_downstream_boundary_readback compactCarrier).left
  have endpointUnary : UnaryHistory transportedEndpoint :=
    unary_cont_closed sourceTargetUnary compactUnary endpointCont
  have endpointSame : hsame transportedEndpoint (append (append source target) compactRow) := by
    cases sameSource
    cases sameTarget
    exact endpointCont
  exact And.intro endpointUnary (And.intro compactCarrier endpointSame)

end BEDC.Derived.NuclearUp
