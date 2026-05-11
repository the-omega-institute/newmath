import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableBHistOperatorCarrier_expectation_transport_readback [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint operator' spectrum'
      expectation' expectationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          Cont operator' spectrum' expectation' ->
            Cont operator' expectation' expectationEndpoint ->
              UnaryHistory expectation' ∧ UnaryHistory expectationEndpoint ∧
                hsame expectation expectation' ∧
                  hsame expectationEndpoint (append operator' expectation') ∧
                    hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier sameOperator sameSpectrum expectationRow' expectationEndpointRow
  have transported :=
    ObservableBHistOperatorCarrier_spectral_transport_stability
      (hilbert := hilbert) (operator := operator) (operator' := operator')
      (spectrum := spectrum) (spectrum' := spectrum') (expectation := expectation)
      (expectation' := expectation') (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (endpoint' := endpoint) (bundle := bundle)
      (pkg := pkg) carrier sameOperator sameSpectrum expectationRow'
      carrier.right.right.right.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.right
  have expectationEndpointUnary : UnaryHistory expectationEndpoint :=
    unary_cont_closed transported.left.right.left transported.left.right.right.right.left
      expectationEndpointRow
  exact
    ⟨transported.left.right.right.right.left,
      expectationEndpointUnary,
      transported.right.left,
      expectationEndpointRow,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.ObservableUp
