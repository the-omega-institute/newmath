import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_determinacy [AskSetup] [PackageSetup]
    {source target target' graph landing routes transport provenance cert cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      CertificateCompilerCarrier source target' graph landing routes transport provenance cert'
        bundle pkg →
        hsame target target' ∧ hsame cert cert' ∧ Cont source graph landing ∧
          Cont landing routes target ∧ Cont landing routes target' ∧ PkgSig bundle cert pkg ∧
            PkgSig bundle cert' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro left right
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, _certMatchesEndpoint, certPkg⟩ := left
  obtain ⟨_sourceUnary', _targetUnary', _graphUnary', _landingUnary', _routesUnary',
    _transportUnary', _provenanceUnary', _sourceGraphLanding', landingRoutesTarget',
    provenanceTargetCert', _certMatchesEndpoint', certPkg'⟩ := right
  have targetSame : hsame target target' :=
    cont_deterministic landingRoutesTarget landingRoutesTarget'
  have certSame : hsame cert cert' :=
    cont_respects_hsame (hsame_refl provenance) targetSame provenanceTargetCert
      provenanceTargetCert'
  exact
    ⟨targetSame, certSame, sourceGraphLanding, landingRoutesTarget, landingRoutesTarget',
      certPkg, certPkg'⟩

end BEDC.Derived.CertificateCompilerUp
