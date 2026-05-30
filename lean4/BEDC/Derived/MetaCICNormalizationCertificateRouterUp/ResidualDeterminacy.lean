import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterResidualDeterminacy [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N residualRead residualRead' frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K S residualRead ->
        Cont K S residualRead' ->
          Cont D U frontierRead ->
            UnaryHistory residualRead ∧ UnaryHistory residualRead' ∧
              UnaryHistory frontierRead ∧ hsame residualRead residualRead' ∧
                Cont D U frontierRead ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier residualRoute residualRoute' frontierRoute
  rcases carrier with
    ⟨_auditUnary, candidateUnary, strongNormUnary, _piAppUnary, closedProjectionUnary,
      generatorUnary, _compilerUnary, _kernelAcceptUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
      _generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary strongNormUnary residualRoute
  have residualUnary' : UnaryHistory residualRead' :=
    unary_cont_closed candidateUnary strongNormUnary residualRoute'
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed closedProjectionUnary generatorUnary frontierRoute
  have residualSame : hsame residualRead residualRead' :=
    cont_deterministic residualRoute residualRoute'
  exact
    ⟨residualUnary, residualUnary', frontierUnary, residualSame, frontierRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
