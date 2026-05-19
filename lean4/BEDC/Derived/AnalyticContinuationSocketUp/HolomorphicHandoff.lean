import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_holomorphic_handoff [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont witness operation output ∧ Cont output continuation consumer)
              (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
              UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory consumer ∧
                Cont source leftOverlap witness ∧ Cont witness operation output ∧
                  Cont output continuation consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier outputContinuationConsumer consumerPkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    _branchUnary, _transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary continuationUnary outputContinuationConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont witness operation output ∧ Cont output continuation consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer
        (And.intro (hsame_refl consumer) consumerUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row _source
      exact And.intro witnessOperationOutput outputContinuationConsumer
    ledger_sound := by
      intro _row source
      exact And.intro source.left consumerPkg
  }
  exact
    ⟨cert, sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary,
      consumerUnary, sourceLeftOverlapWitness, witnessOperationOutput, outputContinuationConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
