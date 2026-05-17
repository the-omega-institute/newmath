import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_right_identity_unit [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget
      compositeTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame identityTarget target →
        Cont landing routes compositeTarget →
          hsame compositeTarget identityTarget ∧ UnaryHistory identityTarget ∧
            UnaryHistory compositeTarget ∧ Cont landing routes compositeTarget ∧
              Cont source graph landing ∧ Cont landing routes target ∧
                hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg
  intro carrier identitySame landingRoutesComposite
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have compositeSame : hsame compositeTarget identityTarget :=
    hsame_trans
      (cont_respects_hsame (hsame_refl landing) (hsame_refl routes)
        landingRoutesComposite landingRoutesTarget)
      (hsame_symm identitySame)
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport targetUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed landingUnary routesUnary landingRoutesComposite
  exact
    ⟨compositeSame, identityUnary, compositeUnary, landingRoutesComposite,
      sourceGraphLanding, landingRoutesTarget, certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
