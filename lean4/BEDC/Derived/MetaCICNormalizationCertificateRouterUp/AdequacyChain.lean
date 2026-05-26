import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterAdequacyChain [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N adequacyRead projectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K P adequacyRead ->
        Cont adequacyRead D projectionRead ->
          UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory D ∧ UnaryHistory adequacyRead ∧
            UnaryHistory projectionRead ∧ Cont K P adequacyRead ∧
              Cont adequacyRead D projectionRead ∧ PkgSig bundle Q pkg ∧
                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier adequacyRoute projectionRoute
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, piAppUnary,
    closedProjectionUnary, _generatorUnary, _compilerUnary, _kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have adequacyUnary : UnaryHistory adequacyRead :=
    unary_cont_closed candidateUnary piAppUnary adequacyRoute
  have projectionUnary : UnaryHistory projectionRead :=
    unary_cont_closed adequacyUnary closedProjectionUnary projectionRoute
  exact
    ⟨candidateUnary, piAppUnary, closedProjectionUnary, adequacyUnary, projectionUnary,
      adequacyRoute, projectionRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
