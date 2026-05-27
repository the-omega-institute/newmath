import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterCriticalPairDischarge [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N residualBoundary confluenceBoundary discharge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K D residualBoundary ->
        Cont residualBoundary G confluenceBoundary ->
          Cont confluenceBoundary L discharge ->
            PkgSig bundle discharge pkg ->
              UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory G ∧ UnaryHistory L ∧
                UnaryHistory residualBoundary ∧ UnaryHistory confluenceBoundary ∧
                  UnaryHistory discharge ∧ Cont K D residualBoundary ∧
                    Cont residualBoundary G confluenceBoundary ∧
                      Cont confluenceBoundary L discharge ∧ PkgSig bundle Q pkg ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle discharge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier residualRoute confluenceRoute dischargeRoute dischargePkg
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    closedProjectionUnary, _generatorUnary, compilerUnary, kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have residualUnary : UnaryHistory residualBoundary :=
    unary_cont_closed candidateUnary closedProjectionUnary residualRoute
  have confluenceUnary : UnaryHistory confluenceBoundary :=
    unary_cont_closed residualUnary compilerUnary confluenceRoute
  have dischargeUnary : UnaryHistory discharge :=
    unary_cont_closed confluenceUnary kernelAcceptUnary dischargeRoute
  exact
    ⟨candidateUnary, closedProjectionUnary, compilerUnary, kernelAcceptUnary,
      residualUnary, confluenceUnary, dischargeUnary, residualRoute, confluenceRoute,
      dischargeRoute, provenancePkg, localNamePkg, dischargePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
