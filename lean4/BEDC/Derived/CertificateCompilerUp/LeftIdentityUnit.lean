import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_left_identity_unit [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget
      compositeTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame identityTarget source →
        Cont identityTarget graph compositeTarget →
          hsame compositeTarget landing ∧ UnaryHistory identityTarget ∧
            UnaryHistory compositeTarget ∧ Cont identityTarget graph compositeTarget ∧
              Cont source graph landing ∧ Cont landing routes target ∧
                hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg
  intro carrier identitySame identityGraphComposite
  obtain ⟨sourceUnary, _targetUnary, graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have compositeSame : hsame compositeTarget landing :=
    cont_respects_hsame identitySame (hsame_refl graph) identityGraphComposite sourceGraphLanding
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed identityUnary graphUnary identityGraphComposite
  exact
    ⟨compositeSame, identityUnary, compositeUnary, identityGraphComposite, sourceGraphLanding,
      landingRoutesTarget, certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
