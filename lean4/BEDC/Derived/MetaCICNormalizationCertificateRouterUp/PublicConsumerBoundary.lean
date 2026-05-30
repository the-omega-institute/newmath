import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterPublicConsumerBoundary [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K U publicRead ->
        Cont publicRead L boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            UnaryHistory K ∧ UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory publicRead ∧
              UnaryHistory boundaryRead ∧ Cont K U publicRead ∧
                Cont publicRead L boundaryRead ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier publicRoute boundaryRoute boundaryPkg
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    _closedProjectionUnary, generatorUnary, _compilerUnary, kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateUnary generatorUnary publicRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed publicReadUnary kernelAcceptUnary boundaryRoute
  exact
    ⟨candidateUnary, generatorUnary, kernelAcceptUnary, publicReadUnary,
      boundaryReadUnary, publicRoute, boundaryRoute, provenancePkg, localNamePkg,
      boundaryPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
