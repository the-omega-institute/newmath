import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterKernelScope [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N scopeRead generatorRead compilerRead
      acceptanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont A K scopeRead ->
        Cont U G generatorRead ->
          Cont G L compilerRead ->
            Cont generatorRead compilerRead acceptanceRead ->
              UnaryHistory A ∧ UnaryHistory K ∧ UnaryHistory scopeRead ∧
                UnaryHistory generatorRead ∧ UnaryHistory compilerRead ∧
                  UnaryHistory acceptanceRead ∧ Cont A K scopeRead ∧
                    Cont U G generatorRead ∧ Cont G L compilerRead ∧
                      Cont generatorRead compilerRead acceptanceRead ∧
                        PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier scopeRoute generatorRoute compilerRoute acceptanceRoute
  obtain ⟨auditUnary, candidateUnary, _strongNormUnary, _piAppUnary, _closedProjectionUnary,
    generatorUnary, compilerUnary, kernelAcceptUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
    _generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed auditUnary candidateUnary scopeRoute
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed generatorUnary compilerUnary generatorRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed compilerUnary kernelAcceptUnary compilerRoute
  have acceptanceReadUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed generatorReadUnary compilerReadUnary acceptanceRoute
  exact
    ⟨auditUnary, candidateUnary, scopeReadUnary, generatorReadUnary, compilerReadUnary,
      acceptanceReadUnary, scopeRoute, generatorRoute, compilerRoute, acceptanceRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
