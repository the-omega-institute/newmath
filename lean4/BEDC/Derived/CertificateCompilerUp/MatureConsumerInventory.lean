import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_mature_consumer_inventory [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget compositeTarget
      tripleTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            PkgSig bundle tripleTarget pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory identityTarget ∧
                  UnaryHistory compositeTarget ∧ UnaryHistory tripleTarget ∧
                    Cont source graph landing ∧ Cont landing routes target ∧
                      Cont target graph compositeTarget ∧
                        Cont compositeTarget routes tripleTarget ∧
                          hsame cert (append provenance target) ∧
                            PkgSig bundle tripleTarget pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier identitySame targetGraphComposite compositeRoutesTriple triplePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, identityUnary,
      compositeUnary, tripleUnary, sourceGraphLanding, landingRoutesTarget,
      targetGraphComposite, compositeRoutesTriple, certMatchesEndpoint, triplePkg⟩

end BEDC.Derived.CertificateCompilerUp
