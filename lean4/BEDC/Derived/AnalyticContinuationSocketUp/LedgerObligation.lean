import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_ledger_obligation [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch consumer →
        Cont consumer transport boundary →
          PkgSig bundle consumer pkg →
            PkgSig bundle boundary pkg →
              UnaryHistory output ∧ UnaryHistory branch ∧ UnaryHistory consumer ∧
                UnaryHistory boundary ∧ Cont output branch consumer ∧
                  Cont consumer transport boundary ∧ Cont branch transport continuation ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                      PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier outputBranchConsumer consumerTransportBoundary consumerPkg boundaryPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary branchUnary outputBranchConsumer
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed consumerUnary transportUnary consumerTransportBoundary
  exact
    ⟨outputUnary,
      branchUnary,
      consumerUnary,
      boundaryUnary,
      outputBranchConsumer,
      consumerTransportBoundary,
      branchTransportContinuation,
      provenancePkg,
      consumerPkg,
      boundaryPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
