import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_classifier_stability_obligation [AskSetup]
    [PackageSetup]
    {source source' leftOverlap leftOverlap' witness witness' operation operation' output
      output' branch branch' transport continuation provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      hsame source source' ->
        hsame leftOverlap leftOverlap' ->
          hsame witness witness' ->
            hsame operation operation' ->
              hsame output output' ->
                hsame branch branch' ->
                  UnaryHistory source' ∧ UnaryHistory leftOverlap' ∧
                    UnaryHistory witness' ∧ UnaryHistory operation' ∧
                      UnaryHistory output' ∧ UnaryHistory branch' ∧
                        Cont source' leftOverlap' witness' ∧
                          Cont witness' operation' output' ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSource sameLeftOverlap sameWitness sameOperation sameOutput sameBranch
  rcases carrier with
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary, branchUnary,
      _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
      sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
      _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, namePkg⟩
  cases sameSource
  cases sameLeftOverlap
  cases sameWitness
  cases sameOperation
  cases sameOutput
  cases sameBranch
  exact
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary, branchUnary,
      sourceLeftOverlapWitness, witnessOperationOutput, provenancePkg, namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
