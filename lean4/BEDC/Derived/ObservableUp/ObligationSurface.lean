import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableBHistOperatorCarrier_namecert_obligation_surface_complete [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint expectationEndpoint
      consumerEndpoint spectralEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        Cont expectationEndpoint endpoint consumerEndpoint ->
          Cont spectrum witness spectralEndpoint ->
            SemanticNameCert (fun h : BHist => hsame h endpoint)
                (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
                hsame ∧
              UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory spectrum ∧
                UnaryHistory expectation ∧ UnaryHistory witness ∧ UnaryHistory consumerEndpoint ∧
                  UnaryHistory spectralEndpoint ∧
                    hsame consumerEndpoint (append (append operator expectation) endpoint) ∧
                      hsame spectralEndpoint (append spectrum witness) ∧
                        hsame endpoint (append provenance ledger) ∧
                          PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow consumerEndpointRow spectralEndpointRow
  have publicRows :=
    ObservableBHistOperatorCarrier_public_row_family
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (consumerEndpoint := consumerEndpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) carrier expectationEndpointRow consumerEndpointRow
      spectralEndpointRow
  have spectralLedgerRows :=
    ObservableBHistOperatorCarrier_hilbert_spectral_ledger_exactness
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) carrier spectralEndpointRow
  have consumerRows :=
    ObservableBHistOperatorCarrier_public_consumer_exhaustion
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (consumerEndpoint := consumerEndpoint) (bundle := bundle) (pkg := pkg) carrier
      expectationEndpointRow consumerEndpointRow
  exact And.intro publicRows.left
    (And.intro spectralLedgerRows.left
      (And.intro spectralLedgerRows.right.left
        (And.intro spectralLedgerRows.right.right.left
          (And.intro spectralLedgerRows.right.right.right.left
            (And.intro spectralLedgerRows.right.right.right.right.left
              (And.intro consumerRows.left
                (And.intro publicRows.right.right.left
                  (And.intro consumerRows.right.left
                    (And.intro publicRows.right.right.right.right.left
                      (And.intro consumerRows.right.right.left
                        consumerRows.right.right.right))))))))))

end BEDC.Derived.ObservableUp
