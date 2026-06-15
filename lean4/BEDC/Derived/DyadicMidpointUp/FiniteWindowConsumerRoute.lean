import BEDC.Derived.DyadicMidpointUp

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMidpointCarrier_finite_window_consumer_route [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont window route consumerRead ->
        PkgSig bundle consumerRead pkg ->
          UnaryHistory window ∧ UnaryHistory route ∧ UnaryHistory consumerRead ∧
            Cont scale midpoint window ∧ Cont branch window route ∧
              Cont window route consumerRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: DyadicMidpointCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨_leftUnary, _rightUnary, scaleUnary, midpointUnary, branchUnary, _windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointExact, _endpointRoute, _scaleRoute, midpointRoute,
    branchRoute, _endpointPkg, provenancePkg, nameCertPkg⟩ := carrier
  have windowClosed : UnaryHistory window :=
    unary_cont_closed scaleUnary midpointUnary midpointRoute
  have routeClosed : UnaryHistory route :=
    unary_cont_closed branchUnary windowClosed branchRoute
  have consumerClosed : UnaryHistory consumerRead :=
    unary_cont_closed windowClosed routeClosed consumerRoute
  exact
    ⟨windowClosed, routeClosed, consumerClosed, midpointRoute, branchRoute, consumerRoute,
      provenancePkg, nameCertPkg, consumerPkg⟩

end BEDC.Derived.DyadicMidpointUp
