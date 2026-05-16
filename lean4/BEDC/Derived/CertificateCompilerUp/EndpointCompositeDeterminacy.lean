import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_composite_determinacy [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpointPrime
      identityTarget compositeTarget tripleTarget bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame endpoint target ->
        hsame endpointPrime target ->
          hsame identityTarget source ->
            Cont target graph compositeTarget ->
              Cont compositeTarget routes tripleTarget ->
                hsame cert bridgeRead ->
                  PkgSig bundle tripleTarget pkg ->
                    hsame endpoint endpointPrime ∧ UnaryHistory identityTarget ∧
                      UnaryHistory compositeTarget ∧ UnaryHistory tripleTarget ∧
                        Cont source graph landing ∧ Cont landing routes target ∧
                          Cont target graph compositeTarget ∧
                            Cont compositeTarget routes tripleTarget ∧
                              hsame bridgeRead (append provenance target) ∧
                                PkgSig bundle tripleTarget pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier endpointSame endpointPrimeSame identitySame targetGraphComposite
    compositeRoutesTriple certBridgeRead triplePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpointPrime :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have bridgeMatchesEndpoint : hsame bridgeRead (append provenance target) :=
    hsame_trans (hsame_symm certBridgeRead) certMatchesEndpoint
  exact
    ⟨endpointDeterminacy, identityUnary, compositeUnary, tripleUnary, sourceGraphLanding,
      landingRoutesTarget, targetGraphComposite, compositeRoutesTriple, bridgeMatchesEndpoint,
      triplePkg⟩

end BEDC.Derived.CertificateCompilerUp
