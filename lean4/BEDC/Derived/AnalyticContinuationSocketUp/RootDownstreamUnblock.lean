import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_root_downstream_unblock [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      outputRead branchRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      Cont output continuation outputRead ->
        Cont outputRead branch branchRead ->
          Cont branchRead provenance publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory branchRead ∧ UnaryHistory publicRead ∧
                Cont witness operation output ∧ Cont output continuation outputRead ∧
                  Cont outputRead branch branchRead ∧ Cont branchRead provenance publicRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier outputContinuationRead readBranchRead branchReadProvenancePublic publicPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, _transportUnary, continuationUnary, provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed outputReadUnary branchUnary readBranchRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary provenanceUnary branchReadProvenancePublic
  exact
    ⟨outputReadUnary, branchReadUnary, publicReadUnary, witnessOperationOutput,
      outputContinuationRead, readBranchRead, branchReadProvenancePublic, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
