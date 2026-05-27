import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterNoInfiniteReductionPublicHandoff [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N residualRead noInfiniteRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K S residualRead ->
        Cont residualRead U noInfiniteRead ->
          Cont noInfiniteRead L handoffRead ->
            PkgSig bundle handoffRead pkg ->
              UnaryHistory K ∧ UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory L ∧
                UnaryHistory residualRead ∧ UnaryHistory noInfiniteRead ∧
                  UnaryHistory handoffRead ∧ Cont K S residualRead ∧
                    Cont residualRead U noInfiniteRead ∧ Cont noInfiniteRead L handoffRead ∧
                      PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                        PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier residualRoute noInfiniteRoute handoffRoute handoffPkg
  obtain ⟨_auditUnary, candidateUnary, strongNormUnary, _piAppUnary,
    _closedProjectionUnary, generatorUnary, _compilerUnary, kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary strongNormUnary residualRoute
  have noInfiniteUnary : UnaryHistory noInfiniteRead :=
    unary_cont_closed residualUnary generatorUnary noInfiniteRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed noInfiniteUnary kernelAcceptUnary handoffRoute
  exact
    ⟨candidateUnary, strongNormUnary, generatorUnary, kernelAcceptUnary, residualUnary,
      noInfiniteUnary, handoffUnary, residualRoute, noInfiniteRoute, handoffRoute,
      provenancePkg, localNamePkg, handoffPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
