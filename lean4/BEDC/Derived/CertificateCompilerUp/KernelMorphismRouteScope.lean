import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_kernelmorphism_route_scope [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead
      publicRead morphismRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph landing landingRead ->
        Cont landingRead transport transportRead ->
          Cont transportRead routes publicRead ->
            Cont publicRead graph morphismRead ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle morphismRead pkg ->
                  UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory transport ∧
                    UnaryHistory routes ∧ UnaryHistory publicRead ∧
                      UnaryHistory morphismRead ∧ Cont source graph landing ∧
                        Cont graph landing landingRead ∧
                          Cont landingRead transport transportRead ∧
                            Cont transportRead routes publicRead ∧
                              Cont publicRead graph morphismRead ∧
                                hsame cert (append provenance target) ∧
                                  PkgSig bundle cert pkg ∧
                                    PkgSig bundle morphismRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier graphLandingRead landingTransportRead transportRoutesPublic
    publicGraphMorphism _publicPkg morphismPkg
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportReadUnary routesUnary transportRoutesPublic
  have morphismReadUnary : UnaryHistory morphismRead :=
    unary_cont_closed publicReadUnary graphUnary publicGraphMorphism
  exact
    ⟨graphUnary, landingUnary, transportUnary, routesUnary, publicReadUnary,
      morphismReadUnary, sourceGraphLanding, graphLandingRead, landingTransportRead,
      transportRoutesPublic, publicGraphMorphism, certMatchesEndpoint, certPkg,
      morphismPkg⟩

end BEDC.Derived.CertificateCompilerUp
