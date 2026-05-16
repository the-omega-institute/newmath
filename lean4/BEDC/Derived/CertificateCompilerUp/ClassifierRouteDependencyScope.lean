import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerClassifier_route_dependency_scope [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' routeRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      Cont routes transport routeRead →
        Cont landing routeRead targetRead →
          PkgSig bundle targetRead pkg →
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory transport ∧
                UnaryHistory routeRead ∧ UnaryHistory targetRead ∧ hsame edge edge' ∧
                  Cont graph edge landing ∧ Cont graph edge' landing ∧
                    Cont routes transport routeRead ∧ Cont landing routeRead targetRead ∧
                      hsame cert (append provenance target) ∧ PkgSig bundle cert pkg ∧
                        PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro classifier routesTransportRead landingRouteTarget targetReadPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', _landingRoutesTarget⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, transportUnary,
    _provenanceUnary, _sourceGraphLanding, _landingRoutesTargetCarrier,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routesUnary transportUnary routesTransportRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed landingUnary routeReadUnary landingRouteTarget
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, transportUnary,
      routeReadUnary, targetReadUnary, edgeSame, graphEdgeLanding, graphEdgeLanding',
      routesTransportRead, landingRouteTarget, certMatchesEndpoint, certPkg,
      targetReadPkg⟩

end BEDC.Derived.CertificateCompilerUp
