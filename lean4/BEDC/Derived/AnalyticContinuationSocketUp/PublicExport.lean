import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_public_export [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
            UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
              UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
                UnaryHistory name ∧ UnaryHistory publicRead ∧ Cont source leftOverlap witness ∧
                  Cont witness operation output ∧ Cont output continuation publicRead ∧
                    Cont branch transport continuation ∧ Cont continuation name provenance ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier outputContinuationPublic publicPkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary,
    branchUnary, transportUnary, continuationUnary, provenanceUnary, nameUnary,
    sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationPublic
  exact
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary, branchUnary,
      transportUnary, continuationUnary, provenanceUnary, nameUnary, publicUnary,
      sourceLeftOverlapWitness, witnessOperationOutput, outputContinuationPublic,
      branchTransportContinuation, continuationNameProvenance, provenancePkg, publicPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
