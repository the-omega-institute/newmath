import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterFrontierResidualAuditHandoff [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N auditRead residualRead frontierRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont A K auditRead ->
        Cont K D residualRead ->
          Cont D U frontierRead ->
            Cont frontierRead L handoffRead ->
              PkgSig bundle handoffRead pkg ->
                UnaryHistory A ∧ UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory U ∧
                  UnaryHistory L ∧ UnaryHistory auditRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory frontierRead ∧ UnaryHistory handoffRead ∧
                      Cont A K auditRead ∧ Cont K D residualRead ∧
                        Cont D U frontierRead ∧ Cont frontierRead L handoffRead ∧
                          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                            PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier auditRoute residualRoute frontierRoute handoffRoute handoffPkg
  obtain ⟨auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    closedProjectionUnary, generatorUnary, _compilerUnary, kernelAcceptUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _candidateStrongNorm, _piAppProjection, _generatorCompiler, _transportReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary candidateUnary auditRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary closedProjectionUnary residualRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed closedProjectionUnary generatorUnary frontierRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed frontierReadUnary kernelAcceptUnary handoffRoute
  exact
    ⟨auditUnary, candidateUnary, closedProjectionUnary, generatorUnary, kernelAcceptUnary,
      auditReadUnary, residualReadUnary, frontierReadUnary, handoffReadUnary, auditRoute,
      residualRoute, frontierRoute, handoffRoute, provenancePkg, localNamePkg,
      handoffPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
