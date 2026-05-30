import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_classifier_transport [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      sourceRead outputRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      hsame sourceRead source ->
        hsame outputRead output ->
          hsame branchRead branch ->
            UnaryHistory sourceRead ∧ UnaryHistory outputRead ∧ UnaryHistory branchRead ∧
              Cont source leftOverlap witness ∧ Cont witness operation output ∧
                Cont branch transport continuation ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSourceRead sameOutputRead sameBranchRead
  obtain ⟨sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, namePkg⟩ :=
    carrier
  exact
    ⟨unary_transport sourceUnary (hsame_symm sameSourceRead),
      unary_transport outputUnary (hsame_symm sameOutputRead),
      unary_transport branchUnary (hsame_symm sameBranchRead),
      sourceLeftOverlapWitness,
      witnessOperationOutput,
      branchTransportContinuation,
      provenancePkg,
      namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
