import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_carrier_admission [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      hsame admitted source ->
        Cont source leftOverlap witness ->
          Cont witness operation output ->
            PkgSig bundle provenance pkg ->
              UnaryHistory admitted ∧ UnaryHistory source ∧ UnaryHistory leftOverlap ∧
                UnaryHistory witness ∧ UnaryHistory output ∧ Cont source leftOverlap witness ∧
                  Cont witness operation output ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameAdmittedSource sourceLeftOverlapWitness witnessOperationOutput provenancePkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, _operationUnary, outputUnary,
    _branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _carrierSourceLeftOverlapWitness, _carrierWitnessOperationOutput,
    _branchTransportContinuation, _outputContinuationProvenance, _continuationNameProvenance,
    _carrierProvenancePkg, namePkg⟩ := carrier
  have admittedUnary : UnaryHistory admitted :=
    unary_transport sourceUnary (hsame_symm sameAdmittedSource)
  exact
    ⟨admittedUnary, sourceUnary, leftOverlapUnary, witnessUnary, outputUnary,
      sourceLeftOverlapWitness, witnessOperationOutput, provenancePkg, namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
