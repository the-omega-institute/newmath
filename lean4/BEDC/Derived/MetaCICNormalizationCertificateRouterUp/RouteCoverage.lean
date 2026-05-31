import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterRouteCoverage [AskSetup] [PackageSetup]
    {audit candidate strongNorm piApp closedProjection generator compiler kernelAccept transport
      replay provenance localName routeRead closedRead generatorRead compilerRead
      acceptanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterPacket audit candidate strongNorm piApp
        closedProjection generator compiler kernelAccept transport replay provenance localName
        bundle pkg →
      Cont candidate strongNorm routeRead →
        Cont candidate closedProjection closedRead →
          Cont candidate generator generatorRead →
            Cont candidate compiler compilerRead →
              Cont candidate kernelAccept acceptanceRead →
                UnaryHistory candidate ∧ UnaryHistory strongNorm ∧ UnaryHistory routeRead ∧
                  UnaryHistory closedRead ∧ UnaryHistory generatorRead ∧
                    UnaryHistory compilerRead ∧ UnaryHistory acceptanceRead ∧
                      Cont candidate strongNorm routeRead ∧
                        Cont candidate closedProjection closedRead ∧
                          Cont candidate generator generatorRead ∧
                            Cont candidate compiler compilerRead ∧
                              Cont candidate kernelAccept acceptanceRead ∧
                                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet routeRoute closedRoute generatorRoute compilerRoute acceptanceRoute
  obtain ⟨_auditUnary, candidateUnary, strongNormUnary, _piAppUnary, closedProjectionUnary,
    generatorUnary, compilerUnary, kernelAcceptUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
    _producerAcceptance, _transportReplay, packageRead⟩ := packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateUnary strongNormUnary routeRoute
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary closedProjectionUnary closedRoute
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed candidateUnary generatorUnary generatorRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed candidateUnary compilerUnary compilerRoute
  have acceptanceReadUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed candidateUnary kernelAcceptUnary acceptanceRoute
  exact
    ⟨candidateUnary, strongNormUnary, routeReadUnary, closedReadUnary, generatorReadUnary,
      compilerReadUnary, acceptanceReadUnary, routeRoute, closedRoute, generatorRoute,
      compilerRoute, acceptanceRoute, packageRead⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
