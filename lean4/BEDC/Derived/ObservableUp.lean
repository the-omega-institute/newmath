import BEDC.Derived.QuantumStateUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.QuantumStateUp

def ObservableBHistOperatorCarrier [AskSetup] [PackageSetup]
    (hilbert operator spectrum expectation witness provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory spectrum ∧
    UnaryHistory expectation ∧ UnaryHistory witness ∧
      Cont operator spectrum expectation ∧ Cont hilbert witness ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem ObservableBHistOperatorCarrier_quantumstate_expectation_boundary [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint stateHilbert
      stateProjective stateVector stateNorm statePhase stateProjectiveEndpoint stateHilbertLedger
      stateProjectiveLedger stateProvenance stateEndpoint expectationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      QuantumStateBHistCarrier stateHilbert stateProjective stateVector stateNorm statePhase
          stateProjectiveEndpoint stateHilbertLedger stateProjectiveLedger stateProvenance
          stateEndpoint bundle pkg ->
        hsame hilbert stateHilbert ->
          Cont operator stateEndpoint expectationEndpoint ->
            UnaryHistory expectationEndpoint ∧
              hsame expectationEndpoint (append operator stateEndpoint) ∧
                hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro operatorCarrier stateCarrier sameHilbert expectationRow
  have stateBoundary :=
    QuantumStateBHistCarrier_hilbert_source_boundary stateCarrier
  have projectiveLedgerRow :
      Cont stateProjective stateProjectiveEndpoint stateProjectiveLedger :=
    stateCarrier.right.right.right.right.right.right.right.right.left
  have endpointRow :
      Cont stateProvenance (append stateHilbertLedger stateProjectiveLedger) stateEndpoint :=
    stateCarrier.right.right.right.right.right.right.right.right.right.right.left
  have projectiveLedgerUnary : UnaryHistory stateProjectiveLedger :=
    unary_cont_closed stateCarrier.right.left stateCarrier.right.right.right.right.right.left
      projectiveLedgerRow
  have combinedLedgerUnary : UnaryHistory (append stateHilbertLedger stateProjectiveLedger) :=
    unary_append_closed stateBoundary.right.right.left projectiveLedgerUnary
  have stateEndpointUnary : UnaryHistory stateEndpoint :=
    unary_cont_closed stateCarrier.right.right.right.right.right.right.left combinedLedgerUnary
      endpointRow
  have _compatibleHilbert : hsame hilbert stateHilbert :=
    sameHilbert
  have expectationEndpointUnary : UnaryHistory expectationEndpoint :=
    unary_cont_closed operatorCarrier.right.left stateEndpointUnary expectationRow
  exact And.intro expectationEndpointUnary
    (And.intro expectationRow
      (And.intro operatorCarrier.right.right.right.right.right.right.right.left
        operatorCarrier.right.right.right.right.right.right.right.right))

end BEDC.Derived.ObservableUp
