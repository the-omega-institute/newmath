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
    UnaryHistory expectation ∧ UnaryHistory witness ∧ UnaryHistory provenance ∧
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
      (And.intro operatorCarrier.right.right.right.right.right.right.right.right.left
        operatorCarrier.right.right.right.right.right.right.right.right.right))

theorem ObservableBHistOperatorCarrier_spectral_data_ledger [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      UnaryHistory expectation ∧ hsame expectation (append operator spectrum) ∧
        UnaryHistory ledger ∧ hsame ledger (append hilbert witness) ∧
          UnaryHistory endpoint ∧ hsame endpoint (append provenance ledger) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have expectationRow : Cont operator spectrum expectation :=
    carrier.right.right.right.right.right.right.left
  have ledgerRow : Cont hilbert witness ledger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have expectationUnary : UnaryHistory expectation :=
    carrier.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.right.right.right.left ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left ledgerUnary endpointRow
  exact And.intro expectationUnary
    (And.intro expectationRow
      (And.intro ledgerUnary
        (And.intro ledgerRow
          (And.intro endpointUnary
            (And.intro endpointRow
              carrier.right.right.right.right.right.right.right.right.right)))))

theorem ObservableBHistOperatorCarrier_spectral_transport_stability [AskSetup]
    [PackageSetup]
    {hilbert operator operator' spectrum spectrum' expectation expectation' witness provenance
      ledger endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          Cont operator' spectrum' expectation' ->
            Cont provenance ledger endpoint' ->
              PkgSig bundle endpoint' pkg ->
                ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness
                    provenance ledger endpoint' bundle pkg ∧
                  hsame expectation expectation' ∧ hsame endpoint endpoint' := by
  intro carrier sameOperator sameSpectrum expectationRow' endpointRow' pkgSig'
  have operatorUnary' : UnaryHistory operator' :=
    unary_transport carrier.right.left sameOperator
  have spectrumUnary' : UnaryHistory spectrum' :=
    unary_transport carrier.right.right.left sameSpectrum
  have expectationUnary' : UnaryHistory expectation' :=
    unary_cont_closed operatorUnary' spectrumUnary' expectationRow'
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameOperator sameSpectrum carrier.right.right.right.right.right.right.left
      expectationRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic carrier.right.right.right.right.right.right.right.right.left endpointRow'
  have carrier' :
      ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness provenance
        ledger endpoint' bundle pkg :=
    And.intro carrier.left
      (And.intro operatorUnary'
        (And.intro spectrumUnary'
          (And.intro expectationUnary'
            (And.intro carrier.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.left
                (And.intro expectationRow'
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro endpointRow' pkgSig'))))))))
  exact And.intro carrier' (And.intro sameExpectation sameEndpoint)

end BEDC.Derived.ObservableUp
