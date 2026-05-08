import BEDC.Derived.BanachUp
import BEDC.Derived.MetricUp
import BEDC.Derived.OperatorIdealUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NuclearUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
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

theorem NuclearLedgerExactness_obligation
    {index coefficient vector partialSum tail operator endpoint : BHist} :
    NuclearRankOnePrefixLedger index coefficient vector partialSum tail ->
      OperatorIdealTraceClassCarrier operator -> Cont operator tail endpoint ->
        UnaryHistory operator ∧ UnaryHistory tail ∧ UnaryHistory endpoint ∧
          (exists support : BHist,
            UnaryHistory support ∧ Cont support BHist.Empty operator ∧
              hsame operator support) ∧
            Cont coefficient vector partialSum ∧ Cont index partialSum tail ∧
              Cont operator tail endpoint := by
  intro ledger operatorCarrier endpointCont
  have ledgerRows := NuclearRankOnePrefixLedger_tail_readback ledger
  have operatorRows := OperatorIdealTraceClass_downstream_boundary_readback operatorCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed operatorRows.left ledgerRows.right.left endpointCont
  exact And.intro operatorRows.left
    (And.intro ledgerRows.right.left
      (And.intro endpointUnary
        (And.intro operatorRows.right
          (And.intro ledgerRows.right.right.left
            (And.intro ledgerRows.right.right.right endpointCont)))))

theorem NuclearDependencyBoundary_obligation
    {source target operator prefixHist index coefficient vector partialSum tail endpoint : BHist} :
    BanachSingletonCarrier source -> BanachSingletonCarrier target ->
      OperatorIdealTraceClassCarrier operator ->
        NuclearRankOnePrefixLedger index coefficient vector partialSum tail ->
          Cont source operator prefixHist -> Cont prefixHist tail endpoint ->
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
              UnaryHistory prefixHist ∧ UnaryHistory tail ∧ UnaryHistory endpoint ∧
                MetricDistanceWitness source BHist.Empty BHist.Empty ∧
                  MetricDistanceWitness target BHist.Empty BHist.Empty ∧
                    Cont source operator prefixHist ∧ Cont prefixHist tail endpoint := by
  intro sourceCarrier targetCarrier operatorCarrier ledger prefixCont endpointCont
  have sourceUnary : UnaryHistory source :=
    unary_transport unary_empty (hsame_symm sourceCarrier.left)
  have targetUnary : UnaryHistory target :=
    unary_transport unary_empty (hsame_symm targetCarrier.left)
  have operatorRows := OperatorIdealTraceClass_downstream_boundary_readback operatorCarrier
  have prefixUnary : UnaryHistory prefixHist :=
    unary_cont_closed sourceUnary operatorRows.left prefixCont
  have ledgerRows := NuclearRankOnePrefixLedger_tail_readback ledger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed prefixUnary ledgerRows.right.left endpointCont
  exact And.intro sourceUnary
    (And.intro targetUnary
      (And.intro operatorRows.left
        (And.intro prefixUnary
          (And.intro ledgerRows.right.left
            (And.intro endpointUnary
                (And.intro sourceCarrier.right
                  (And.intro targetCarrier.right
                    (And.intro prefixCont endpointCont))))))))

theorem NuclearRankOnePrefixLedger_semantic_name_certificate
    {index coefficient vector partialSum tail : BHist} :
    NuclearRankOnePrefixLedger index coefficient vector partialSum tail ->
      SemanticNameCert
        (fun endpoint : BHist =>
          NuclearRankOnePrefixLedger index coefficient vector partialSum endpoint)
        (fun endpoint : BHist =>
          NuclearRankOnePrefixLedger index coefficient vector partialSum endpoint)
        (fun endpoint : BHist =>
          NuclearRankOnePrefixLedger index coefficient vector partialSum endpoint)
        hsame := by
  intro ledger
  exact {
    core := {
      carrier_inhabited := Exists.intro tail ledger
      equiv_refl := by
        intro endpoint _source
        exact hsame_refl endpoint
      equiv_symm := by
        intro _endpoint _endpoint' sameEndpoint
        exact hsame_symm sameEndpoint
      equiv_trans := by
        intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro endpoint endpoint' sameEndpoint sourceLedger
        exact And.intro sourceLedger.left
          (And.intro sourceLedger.right.left
            (And.intro sourceLedger.right.right.left
              (And.intro sourceLedger.right.right.right.left
                (cont_result_hsame_transport sourceLedger.right.right.right.right
                  sameEndpoint))))
    }
    pattern_sound := by
      intro _endpoint source
      exact source
    ledger_sound := by
      intro _endpoint source
      exact source
  }

end BEDC.Derived.NuclearUp
