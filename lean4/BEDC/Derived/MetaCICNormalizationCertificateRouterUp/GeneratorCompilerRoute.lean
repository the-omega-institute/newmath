import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterGeneratorCompilerRoute [AskSetup] [PackageSetup]
    {A K S P D U G L H C Q N generatorRead provenanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier A K S P D U G L H C Q N bundle pkg →
      Cont U G generatorRead →
        Cont H C provenanceRead →
          UnaryHistory K ∧ UnaryHistory U ∧ UnaryHistory G ∧ UnaryHistory L ∧
            UnaryHistory generatorRead ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory provenanceRead ∧ Cont U G generatorRead ∧ Cont U G L ∧
                Cont H C provenanceRead ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier generatorRoute provenanceRoute
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, _piAppUnary,
    _closedProjectionUnary, generatorUnary, compilerUnary, kernelAcceptUnary, transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
    generatorCompiler, _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed generatorUnary compilerUnary generatorRoute
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed transportUnary replayUnary provenanceRoute
  exact
    ⟨candidateUnary, generatorUnary, compilerUnary, kernelAcceptUnary, generatorReadUnary,
      transportUnary, replayUnary, provenanceReadUnary, generatorRoute, generatorCompiler,
      provenanceRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
