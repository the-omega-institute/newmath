import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_carrier_source_obligation [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      sourceRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame sourceRead source →
        Cont witness operation operationRead →
          PkgSig bundle operationRead pkg →
            UnaryHistory sourceRead ∧ UnaryHistory source ∧ UnaryHistory leftOverlap ∧
              UnaryHistory witness ∧ UnaryHistory operationRead ∧
                Cont source leftOverlap witness ∧ Cont witness operation operationRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSourceRead witnessOperationRead operationPkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    _branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    sourceLeftOverlapWitness, _witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, namePkg⟩ :=
    carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport sourceUnary (hsame_symm sameSourceRead)
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed witnessUnary operationUnary witnessOperationRead
  exact
    ⟨sourceReadUnary, sourceUnary, leftOverlapUnary, witnessUnary, operationReadUnary,
      sourceLeftOverlapWitness, witnessOperationRead, provenancePkg, namePkg, operationPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
