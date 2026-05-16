import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_real_completion_selector_route [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      selectorRead selectorRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg ->
      Cont window regseq selectorRead ->
        Cont selectorRead endpoint selectorRoute ->
          PkgSig bundle selectorRoute pkg ->
            UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                UnaryHistory selectorRead ∧ UnaryHistory selectorRoute ∧
                  Cont precision window dyadic ∧ Cont dyadic regseq sealRow ∧
                    Cont window regseq selectorRead ∧ Cont selectorRead endpoint selectorRoute ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle selectorRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowRegseqSelector selectorEndpointRoute selectorRoutePkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute,
    _routeProvenanceEndpoint, _endpointLocalCert, endpointPkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowUnary regseqUnary windowRegseqSelector
  have selectorRouteUnary : UnaryHistory selectorRoute :=
    unary_cont_closed selectorUnary endpointUnary selectorEndpointRoute
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, endpointUnary,
      selectorUnary, selectorRouteUnary, precisionWindowDyadic, dyadicRegseqSeal,
      windowRegseqSelector, selectorEndpointRoute, endpointPkg, selectorRoutePkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
