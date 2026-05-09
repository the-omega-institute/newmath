import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.QuantumStateUp

theorem ObservableBHistOperatorCarrier_spectral_state_source_coherence [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint stateHilbert
      stateProjective stateVector stateNorm statePhase stateProjectiveEndpoint stateHilbertLedger
      stateProjectiveLedger stateProvenance stateEndpoint expectationEndpoint spectralEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      QuantumStateBHistCarrier stateHilbert stateProjective stateVector stateNorm statePhase
          stateProjectiveEndpoint stateHilbertLedger stateProjectiveLedger stateProvenance
          stateEndpoint bundle pkg ->
        hsame hilbert stateHilbert ->
          Cont operator stateEndpoint expectationEndpoint ->
            Cont spectrum witness spectralEndpoint ->
              UnaryHistory spectralEndpoint ∧ UnaryHistory expectationEndpoint ∧
                hsame spectralEndpoint (append spectrum witness) ∧
                  hsame expectationEndpoint (append operator stateEndpoint) ∧
                    hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro operatorCarrier stateCarrier sameHilbert expectationEndpointRow spectralEndpointRow
  have spectralRows :=
    ObservableBHistOperatorCarrier_hilbert_spectral_ledger_exactness
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) operatorCarrier spectralEndpointRow
  have expectationRows :=
    ObservableBHistOperatorCarrier_quantumstate_expectation_boundary
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (stateHilbert := stateHilbert)
      (stateProjective := stateProjective) (stateVector := stateVector)
      (stateNorm := stateNorm) (statePhase := statePhase)
      (stateProjectiveEndpoint := stateProjectiveEndpoint)
      (stateHilbertLedger := stateHilbertLedger)
      (stateProjectiveLedger := stateProjectiveLedger) (stateProvenance := stateProvenance)
      (stateEndpoint := stateEndpoint) (expectationEndpoint := expectationEndpoint)
      (bundle := bundle) (pkg := pkg) operatorCarrier stateCarrier sameHilbert
      expectationEndpointRow
  exact And.intro spectralRows.right.right.right.right.right.left
    (And.intro expectationRows.left
      (And.intro spectralRows.right.right.right.right.right.right.right.left
        (And.intro expectationRows.right.left
          (And.intro spectralRows.right.right.right.right.right.right.right.right.left
            spectralRows.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.ObservableUp
