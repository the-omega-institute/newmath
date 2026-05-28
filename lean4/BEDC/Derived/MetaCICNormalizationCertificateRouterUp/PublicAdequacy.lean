import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.CriticalPairDischarge
import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.FrontierResidualAuditHandoff
import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.PublicConsumerBoundary
import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.ResidualCandidateCoverage
import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.RouteCoverage

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterPublicAdequacy [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N publicRead residualRead boundaryRead adequacyRead
      projectionRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K U publicRead ->
        Cont K D residualRead ->
          Cont residualRead G boundaryRead ->
            Cont K P adequacyRead ->
              Cont adequacyRead D projectionRead ->
                Cont projectionRead L handoffRead ->
                  PkgSig bundle boundaryRead pkg ->
                    PkgSig bundle handoffRead pkg ->
                      UnaryHistory K ∧ UnaryHistory U ∧ UnaryHistory D ∧
                        UnaryHistory G ∧ UnaryHistory L ∧ UnaryHistory P ∧
                          UnaryHistory publicRead ∧ UnaryHistory residualRead ∧
                            UnaryHistory boundaryRead ∧ UnaryHistory adequacyRead ∧
                              UnaryHistory projectionRead ∧ UnaryHistory handoffRead ∧
                                Cont K U publicRead ∧ Cont K D residualRead ∧
                                  Cont residualRead G boundaryRead ∧ Cont K P adequacyRead ∧
                                    Cont adequacyRead D projectionRead ∧
                                      Cont projectionRead L handoffRead ∧
                                        PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                                          PkgSig bundle boundaryRead pkg ∧
                                            PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier publicRoute residualRoute boundaryRoute adequacyRoute projectionRoute
    handoffRoute boundaryPkg handoffPkg
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, piAppUnary,
    closedProjectionUnary, generatorUnary, compilerUnary, kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateUnary generatorUnary publicRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary closedProjectionUnary residualRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed residualReadUnary compilerUnary boundaryRoute
  have adequacyReadUnary : UnaryHistory adequacyRead :=
    unary_cont_closed candidateUnary piAppUnary adequacyRoute
  have projectionReadUnary : UnaryHistory projectionRead :=
    unary_cont_closed adequacyReadUnary closedProjectionUnary projectionRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed projectionReadUnary kernelAcceptUnary handoffRoute
  exact
    ⟨candidateUnary, generatorUnary, closedProjectionUnary, compilerUnary,
      kernelAcceptUnary, piAppUnary, publicReadUnary, residualReadUnary,
      boundaryReadUnary, adequacyReadUnary, projectionReadUnary, handoffReadUnary,
      publicRoute, residualRoute, boundaryRoute, adequacyRoute, projectionRoute,
      handoffRoute, provenancePkg, localNamePkg, boundaryPkg, handoffPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
