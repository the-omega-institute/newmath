import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableNameCert_obligation_surface [AskSetup] [PackageSetup]
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
  have endpointRow : hsame endpoint (append provenance ledger) :=
    carrier.right.right.right.right.right.right.right.right.left
  exact And.intro publicRows.left
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro carrier.right.right.right.right.left
              (And.intro publicRows.right.left
                (And.intro publicRows.right.right.left
                  (And.intro publicRows.right.right.right.left
                    (And.intro publicRows.right.right.right.right.left
                      (And.intro endpointRow publicRows.right.right.right.right.right))))))))))

end BEDC.Derived.ObservableUp
