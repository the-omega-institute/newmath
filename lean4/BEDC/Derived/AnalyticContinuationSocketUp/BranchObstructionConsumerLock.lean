import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_branch_obstruction_consumer_lock [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      branchRead boundary consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame branchRead branch →
        Cont branchRead transport boundary →
          Cont boundary name consumer →
            PkgSig bundle consumer pkg →
              UnaryHistory branch ∧ UnaryHistory branchRead ∧ UnaryHistory boundary ∧
                UnaryHistory consumer ∧ Cont branchRead transport boundary ∧
                  Cont boundary name consumer ∧ Cont branch transport continuation ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameBranchRead branchReadTransportBoundary boundaryNameConsumer consumerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, _outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_transport branchUnary (hsame_symm sameBranchRead)
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed branchReadUnary transportUnary branchReadTransportBoundary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed boundaryUnary nameUnary boundaryNameConsumer
  exact
    ⟨branchUnary, branchReadUnary, boundaryUnary, consumerUnary, branchReadTransportBoundary,
      boundaryNameConsumer, branchTransportContinuation, provenancePkg, consumerPkg⟩

theorem AnalyticContinuationSocketCarrier_branch_obstruction_nonexport [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      hsame consumer branch ->
        PkgSig bundle consumer pkg ->
          UnaryHistory consumer ∧ UnaryHistory branch ∧ Cont branch transport continuation ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameConsumerBranch consumerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, _outputUnary,
    branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_transport branchUnary (hsame_symm sameConsumerBranch)
  exact
    ⟨consumerUnary, branchUnary, branchTransportContinuation, provenancePkg, consumerPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
