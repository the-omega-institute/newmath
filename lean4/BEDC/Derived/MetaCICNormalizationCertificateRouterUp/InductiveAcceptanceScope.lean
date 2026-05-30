import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterInductiveAcceptanceScope [AskSetup]
    [PackageSetup] {A K S P D U G L H C Q N acceptanceRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont G L acceptanceRead ->
        Cont H C routeRead ->
          UnaryHistory A ∧ UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory U ∧
            UnaryHistory G ∧ UnaryHistory L ∧ UnaryHistory acceptanceRead ∧
              UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory routeRead ∧
                Cont G L acceptanceRead ∧ Cont U G L ∧ Cont H C routeRead ∧
                  PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier acceptanceRoute routeRoute
  obtain ⟨auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    closedProjectionUnary, generatorUnary, compilerUnary, kernelAcceptUnary,
    transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _candidateStrongNorm,
    _piAppProjection, generatorCompilerAccept, _transportReplay, provenancePkg,
    localNamePkg⟩ := carrier
  have acceptanceReadUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed compilerUnary kernelAcceptUnary acceptanceRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed transportUnary replayUnary routeRoute
  exact
    ⟨auditUnary, candidateUnary, closedProjectionUnary, generatorUnary, compilerUnary,
      kernelAcceptUnary, acceptanceReadUnary, transportUnary, replayUnary, routeReadUnary,
      acceptanceRoute, generatorCompilerAccept, routeRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
