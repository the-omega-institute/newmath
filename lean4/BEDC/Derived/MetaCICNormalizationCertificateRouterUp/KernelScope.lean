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

theorem MetaCICNormalizationCertificateRouterScopedKernelRoute [AskSetup] [PackageSetup]
    {audit candidate strongNorm piApp closedProjection generator compiler kernelAccept transport
      replay provenance localName scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier audit candidate strongNorm piApp
        closedProjection generator compiler kernelAccept transport replay provenance localName
        bundle pkg ->
      Cont transport replay scopedRead ->
        PkgSig bundle scopedRead pkg ->
          UnaryHistory candidate ∧ UnaryHistory strongNorm ∧ UnaryHistory piApp ∧
            UnaryHistory closedProjection ∧ UnaryHistory generator ∧ UnaryHistory compiler ∧
              UnaryHistory kernelAccept ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
                UnaryHistory scopedRead ∧ Cont candidate strongNorm piApp ∧
                  Cont piApp closedProjection transport ∧ Cont generator compiler kernelAccept ∧
                    Cont transport replay scopedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier scopedRoute scopedPkg
  obtain ⟨_auditUnary, candidateUnary, strongNormUnary, piAppUnary,
    closedProjectionUnary, generatorUnary, compilerUnary, kernelAcceptUnary, transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, candidateStrongNorm, piAppProjection,
    generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed transportUnary replayUnary scopedRoute
  exact
    ⟨candidateUnary, strongNormUnary, piAppUnary, closedProjectionUnary, generatorUnary,
      compilerUnary, kernelAcceptUnary, transportUnary, replayUnary, scopedUnary,
      candidateStrongNorm, piAppProjection, generatorCompiler, scopedRoute, provenancePkg,
      localNamePkg, scopedPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
