import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CertificateCompilerCarrier_endpoint_route_pullback_determinacy [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpointPrime
      landingRead transportRead publicRead morphismRead inverseRead inverseReadPrime :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame endpoint target →
        hsame endpointPrime target →
          Cont graph landing landingRead →
            Cont landingRead transport transportRead →
              Cont transportRead routes publicRead →
                Cont publicRead graph morphismRead →
                  Cont morphismRead cert inverseRead →
                    Cont morphismRead cert inverseReadPrime →
                      PkgSig bundle inverseRead pkg →
                        PkgSig bundle inverseReadPrime pkg →
                          hsame endpoint endpointPrime ∧ hsame inverseRead inverseReadPrime ∧
                            Cont source graph landing ∧ Cont landing routes target ∧
                              Cont publicRead graph morphismRead ∧
                                hsame cert (append provenance target) ∧
                                  PkgSig bundle inverseRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro carrier endpointSame endpointPrimeSame _graphLandingRead _landingTransportRead
    _transportRoutesPublic publicGraphMorphism morphismCertInverse morphismCertInversePrime
    inversePkg _inversePrimePkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpointPrime :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have inverseDeterminacy : hsame inverseRead inverseReadPrime :=
    cont_deterministic morphismCertInverse morphismCertInversePrime
  exact
    ⟨endpointDeterminacy, inverseDeterminacy, sourceGraphLanding, landingRoutesTarget,
      publicGraphMorphism, certMatchesEndpoint, inversePkg⟩

end BEDC.Derived.CertificateCompilerUp
