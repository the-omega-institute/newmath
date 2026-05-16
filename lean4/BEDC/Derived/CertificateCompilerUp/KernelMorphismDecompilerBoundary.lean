import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_kernelmorphism_decompiler_boundary [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead
      publicRead morphismRead inverseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph landing landingRead ->
        Cont landingRead transport transportRead ->
          Cont transportRead routes publicRead ->
            Cont publicRead graph morphismRead ->
              Cont morphismRead cert inverseRead ->
                PkgSig bundle publicRead pkg ->
                  PkgSig bundle morphismRead pkg ->
                    PkgSig bundle inverseRead pkg ->
                      UnaryHistory morphismRead ∧ UnaryHistory inverseRead ∧
                        Cont publicRead graph morphismRead ∧
                          Cont morphismRead cert inverseRead ∧
                            hsame cert (append provenance target) ∧
                              PkgSig bundle inverseRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier graphLandingRead landingTransportRead transportRoutesPublic
    publicGraphMorphism morphismCertInverse _publicPkg _morphismPkg inversePkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, transportUnary,
    provenanceUnary, _sourceGraphLanding, _landingRoutesTarget, provenanceTargetCert,
    certMatchesEndpoint, _certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportReadUnary routesUnary transportRoutesPublic
  have morphismReadUnary : UnaryHistory morphismRead :=
    unary_cont_closed publicReadUnary graphUnary publicGraphMorphism
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have inverseReadUnary : UnaryHistory inverseRead :=
    unary_cont_closed morphismReadUnary certUnary morphismCertInverse
  exact
    ⟨morphismReadUnary, inverseReadUnary, publicGraphMorphism, morphismCertInverse,
      certMatchesEndpoint, inversePkg⟩

end BEDC.Derived.CertificateCompilerUp
