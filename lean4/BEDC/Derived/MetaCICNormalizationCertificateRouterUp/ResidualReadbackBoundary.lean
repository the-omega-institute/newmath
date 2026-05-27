import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterResidualReadbackBoundary [AskSetup]
    [PackageSetup]
    {A K S P D U G L H C Q N residualRead closedRead generatorRead compilerRead
      acceptanceRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg ->
      Cont K S residualRead ->
        Cont K D closedRead ->
          Cont K U generatorRead ->
            Cont generatorRead G compilerRead ->
              Cont compilerRead L acceptanceRead ->
                Cont acceptanceRead N readbackRead ->
                  PkgSig bundle readbackRead pkg ->
                    UnaryHistory residualRead ∧ UnaryHistory closedRead ∧
                      UnaryHistory generatorRead ∧ UnaryHistory compilerRead ∧
                        UnaryHistory acceptanceRead ∧ UnaryHistory readbackRead ∧
                          Cont K S residualRead ∧ Cont K D closedRead ∧
                            Cont K U generatorRead ∧ Cont generatorRead G compilerRead ∧
                              Cont compilerRead L acceptanceRead ∧
                                Cont acceptanceRead N readbackRead ∧ PkgSig bundle Q pkg ∧
                                  PkgSig bundle N pkg ∧ PkgSig bundle readbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier residualRoute closedRoute generatorRoute compilerRoute acceptanceRoute
    readbackRoute readbackPkg
  obtain ⟨_auditUnary, candidateUnary, strongNormUnary, _piAppUnary, closedProjectionUnary,
    generatorUnary, compilerUnary, kernelAcceptUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _candidateStrongNorm, _piAppProjection,
    _generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary strongNormUnary residualRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary closedProjectionUnary closedRoute
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed candidateUnary generatorUnary generatorRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed generatorReadUnary compilerUnary compilerRoute
  have acceptanceReadUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed compilerReadUnary kernelAcceptUnary acceptanceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed acceptanceReadUnary localNameUnary readbackRoute
  exact
    ⟨residualUnary, closedUnary, generatorReadUnary, compilerReadUnary, acceptanceReadUnary,
      readbackReadUnary, residualRoute, closedRoute, generatorRoute, compilerRoute,
      acceptanceRoute, readbackRoute, provenancePkg, localNamePkg, readbackPkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
