import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_decompiler_handoff_determinacy [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpointPrime
      identityTarget compositeTarget tripleTarget inverseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame endpoint target ->
        hsame endpointPrime target ->
          hsame identityTarget source ->
            Cont target graph compositeTarget ->
              Cont compositeTarget routes tripleTarget ->
                Cont tripleTarget cert inverseRead ->
                  PkgSig bundle inverseRead pkg ->
                    hsame endpoint endpointPrime ∧ UnaryHistory inverseRead ∧
                      Cont source graph landing ∧ Cont landing routes target ∧
                        Cont target graph compositeTarget ∧
                          Cont compositeTarget routes tripleTarget ∧
                            Cont tripleTarget cert inverseRead ∧
                              hsame cert (append provenance target) ∧
                                PkgSig bundle inverseRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier endpointSame endpointPrimeSame _identitySame targetGraphComposite
    compositeRoutesTriple tripleCertInverse inversePkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpointPrime :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have inverseUnary : UnaryHistory inverseRead :=
    unary_cont_closed tripleUnary certUnary tripleCertInverse
  exact
    ⟨endpointDeterminacy, inverseUnary, sourceGraphLanding, landingRoutesTarget,
      targetGraphComposite, compositeRoutesTriple, tripleCertInverse, certMatchesEndpoint,
      inversePkg⟩

end BEDC.Derived.CertificateCompilerUp
