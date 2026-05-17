import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_kernelmorphism_roundtrip [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpointPrime
      morphismRead inverseRead returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame endpoint target ->
        hsame endpointPrime target ->
          Cont target graph morphismRead ->
            Cont morphismRead cert inverseRead ->
              Cont inverseRead provenance returnRead ->
                PkgSig bundle returnRead pkg ->
                  hsame endpoint endpointPrime ∧ UnaryHistory morphismRead ∧
                    UnaryHistory inverseRead ∧ UnaryHistory returnRead ∧
                      Cont target graph morphismRead ∧ Cont morphismRead cert inverseRead ∧
                        Cont inverseRead provenance returnRead ∧
                          hsame cert (append provenance target) ∧
                            PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier endpointSame endpointPrimeSame targetGraphMorphism morphismCertInverse
    inverseProvenanceReturn returnPkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, _landingUnary, _routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpointPrime :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have morphismUnary : UnaryHistory morphismRead :=
    unary_cont_closed targetUnary graphUnary targetGraphMorphism
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have inverseUnary : UnaryHistory inverseRead :=
    unary_cont_closed morphismUnary certUnary morphismCertInverse
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed inverseUnary provenanceUnary inverseProvenanceReturn
  exact
    ⟨endpointDeterminacy, morphismUnary, inverseUnary, returnUnary, targetGraphMorphism,
      morphismCertInverse, inverseProvenanceReturn, certMatchesEndpoint, returnPkg⟩

end BEDC.Derived.CertificateCompilerUp
