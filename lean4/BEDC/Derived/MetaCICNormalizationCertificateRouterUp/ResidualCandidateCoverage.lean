import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterResidualCandidateCoverage [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N residualRead adequacyRead projectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg →
      Cont K S residualRead →
        Cont K P adequacyRead →
          Cont adequacyRead D projectionRead →
            UnaryHistory K ∧ UnaryHistory S ∧ UnaryHistory P ∧ UnaryHistory D ∧
              UnaryHistory residualRead ∧ UnaryHistory adequacyRead ∧
                UnaryHistory projectionRead ∧ Cont K S residualRead ∧
                  Cont K P adequacyRead ∧ Cont adequacyRead D projectionRead ∧
                    PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier residualRoute adequacyRoute projectionRoute
  rcases carrier with
    ⟨_auditUnary, candidateUnary, strongNormUnary, piAppUnary, closedProjectionUnary,
      _generatorUnary, _compilerUnary, _kernelAcceptUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
      _generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary strongNormUnary residualRoute
  have adequacyUnary : UnaryHistory adequacyRead :=
    unary_cont_closed candidateUnary piAppUnary adequacyRoute
  have projectionUnary : UnaryHistory projectionRead :=
    unary_cont_closed adequacyUnary closedProjectionUnary projectionRoute
  exact
    ⟨candidateUnary, strongNormUnary, piAppUnary, closedProjectionUnary, residualUnary,
      adequacyUnary, projectionUnary, residualRoute, adequacyRoute, projectionRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
