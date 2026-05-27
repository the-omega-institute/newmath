import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterProjectionCoverage [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N projectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N
      bundle pkg)
    (projectionRoute : Cont K D projectionRead) :
    UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory projectionRead ∧
      Cont K D projectionRead ∧ hsame projectionRead (append K D) ∧
        PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame append
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    closedProjectionUnary, _generatorUnary, _compilerUnary, _kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have projectionReadUnary : UnaryHistory projectionRead :=
    unary_cont_closed candidateUnary closedProjectionUnary projectionRoute
  have projectionExact : hsame projectionRead (append K D) := by
    cases projectionRoute
    exact hsame_refl _
  exact
    ⟨candidateUnary, closedProjectionUnary, projectionReadUnary, projectionRoute,
      projectionExact, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
