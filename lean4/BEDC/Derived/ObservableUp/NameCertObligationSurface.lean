import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableBHistOperatorCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
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
              ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness
                provenance ledger endpoint bundle pkg ∧
                UnaryHistory consumerEndpoint ∧ UnaryHistory spectralEndpoint ∧
                  hsame consumerEndpoint (append (append operator expectation) endpoint) ∧
                    hsame spectralEndpoint (append spectrum witness) ∧
                      PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow consumerEndpointRow spectralEndpointRow
  have rows :=
    ObservableBHistOperatorCarrier_public_row_family
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (consumerEndpoint := consumerEndpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) carrier expectationEndpointRow consumerEndpointRow
      spectralEndpointRow
  exact And.intro rows.left
    (And.intro carrier
      (And.intro rows.right.left
        (And.intro rows.right.right.left
          (And.intro rows.right.right.right.left
            (And.intro rows.right.right.right.right.left rows.right.right.right.right.right)))))

end BEDC.Derived.ObservableUp
