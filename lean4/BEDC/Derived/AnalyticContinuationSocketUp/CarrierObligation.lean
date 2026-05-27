import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame carrierRead (append source (append leftOverlap witness)) →
        UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
          UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
            UnaryHistory carrierRead ∧
              hsame carrierRead (append source (append leftOverlap witness)) ∧
                Cont source leftOverlap witness ∧ Cont witness operation output ∧
                  Cont branch transport continuation ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameCarrierRead
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary,
    branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have overlapWitnessUnary : UnaryHistory (append leftOverlap witness) :=
    unary_append_closed leftOverlapUnary witnessUnary
  have carrierReadAppendUnary :
      UnaryHistory (append source (append leftOverlap witness)) :=
    unary_append_closed sourceUnary overlapWitnessUnary
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_transport carrierReadAppendUnary (hsame_symm sameCarrierRead)
  exact
    ⟨sourceUnary,
      leftOverlapUnary,
      witnessUnary,
      operationUnary,
      outputUnary,
      branchUnary,
      carrierReadUnary,
      sameCarrierRead,
      sourceLeftOverlapWitness,
      witnessOperationOutput,
      branchTransportContinuation,
      provenancePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
