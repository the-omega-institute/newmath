import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_route_determinacy [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' route route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      Cont edge routes route ->
        Cont edge' routes route' ->
          UnaryHistory route /\ UnaryHistory route' /\ hsame route route' /\ hsame edge edge' /\
            Cont edge routes route /\ Cont edge' routes route' /\
              hsame cert (append provenance target) /\ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro classifier edgeRoutesRoute edgePrimeRoutesRoute
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, _graphEdgeLanding,
    _graphEdgeLanding', _landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed edgeUnary routesUnary edgeRoutesRoute
  have routePrimeUnary : UnaryHistory route' :=
    unary_cont_closed edgeUnary' routesUnary edgePrimeRoutesRoute
  have routeSame : hsame route route' :=
    cont_respects_hsame edgeSame (hsame_refl routes) edgeRoutesRoute edgePrimeRoutesRoute
  exact
    ⟨routeUnary, routePrimeUnary, routeSame, edgeSame, edgeRoutesRoute, edgePrimeRoutesRoute,
      certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
