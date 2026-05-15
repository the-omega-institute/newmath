import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_public_consumer_boundary [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph landing landingRead ->
        Cont landingRead transport transportRead ->
          Cont transportRead routes publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory routes ∧
                UnaryHistory transport ∧ UnaryHistory landingRead ∧
                  UnaryHistory transportRead ∧ UnaryHistory publicRead ∧
                    Cont source graph landing ∧ Cont graph landing landingRead ∧
                      Cont landingRead transport transportRead ∧
                        Cont transportRead routes publicRead ∧ PkgSig bundle cert pkg ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier graphLandingRead landingTransportRead transportRoutesPublic publicPkg
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportReadUnary routesUnary transportRoutesPublic
  exact
    ⟨graphUnary, landingUnary, routesUnary, transportUnary, landingReadUnary,
      transportReadUnary, publicReadUnary, sourceGraphLanding, graphLandingRead,
      landingTransportRead, transportRoutesPublic, certPkg, publicPkg⟩

theorem CertificateCompilerCarrier_downstream_stage_unblock_package [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead
      publicRead stageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph landing landingRead ->
        Cont landingRead transport transportRead ->
          Cont transportRead routes publicRead ->
            Cont publicRead cert stageRead ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle stageRead pkg ->
                  UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory routes ∧
                    UnaryHistory transport ∧ UnaryHistory landingRead ∧
                      UnaryHistory transportRead ∧ UnaryHistory publicRead ∧
                        UnaryHistory stageRead ∧ Cont source graph landing ∧
                          Cont graph landing landingRead ∧
                            Cont landingRead transport transportRead ∧
                              Cont transportRead routes publicRead ∧
                                Cont publicRead cert stageRead ∧
                                  hsame cert (append provenance target) ∧
                                    PkgSig bundle cert pkg ∧ PkgSig bundle publicRead pkg ∧
                                      PkgSig bundle stageRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier graphLandingRead landingTransportRead transportRoutesPublic publicCertStage
    publicPkg stagePkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportReadUnary routesUnary transportRoutesPublic
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed publicReadUnary certUnary publicCertStage
  exact
    ⟨graphUnary, landingUnary, routesUnary, transportUnary, landingReadUnary,
      transportReadUnary, publicReadUnary, stageReadUnary, sourceGraphLanding,
        graphLandingRead, landingTransportRead, transportRoutesPublic, publicCertStage,
          certMatchesEndpoint, certPkg, publicPkg, stagePkg⟩

end BEDC.Derived.CertificateCompilerUp
