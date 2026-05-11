import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableBHistOperatorCarrier_public_surface_bridge_boundary [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint expectationEndpoint
      consumerEndpoint spectralEndpoint bridgeEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        Cont expectationEndpoint endpoint consumerEndpoint ->
          Cont spectrum witness spectralEndpoint ->
            Cont consumerEndpoint spectralEndpoint bridgeEndpoint ->
              UnaryHistory bridgeEndpoint ∧ hsame bridgeEndpoint
                  (append consumerEndpoint spectralEndpoint) ∧
                hsame consumerEndpoint (append (append operator expectation) endpoint) ∧
                  hsame spectralEndpoint (append spectrum witness) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow consumerEndpointRow spectralEndpointRow bridgeEndpointRow
  have publicRows :=
    ObservableBHistOperatorCarrier_public_row_family
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (consumerEndpoint := consumerEndpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) carrier expectationEndpointRow consumerEndpointRow
      spectralEndpointRow
  have bridgeEndpointUnary : UnaryHistory bridgeEndpoint :=
    unary_cont_closed publicRows.right.left publicRows.right.right.left bridgeEndpointRow
  exact And.intro bridgeEndpointUnary
    (And.intro bridgeEndpointRow
      (And.intro publicRows.right.right.right.left
        (And.intro publicRows.right.right.right.right.left publicRows.right.right.right.right.right)))

end BEDC.Derived.ObservableUp
