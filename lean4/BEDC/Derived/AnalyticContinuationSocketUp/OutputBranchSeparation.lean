import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_output_branch_separation [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      outputRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      Cont output continuation outputRead ->
        Cont output branch branchRead ->
          PkgSig bundle outputRead pkg ->
            PkgSig bundle branchRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    Cont witness operation output ∧ Cont output continuation outputRead)
                  (fun row : BHist => hsame row outputRead ∧ PkgSig bundle outputRead pkg)
                  hsame ∧
                SemanticNameCert
                    (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont output branch branchRead ∧ Cont branch transport continuation)
                    (fun row : BHist => hsame row branchRead ∧ PkgSig bundle branchRead pkg)
                    hsame ∧
                  UnaryHistory outputRead ∧ UnaryHistory branchRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier outputContinuationRead outputBranchRead outputReadPkg branchReadPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed outputUnary branchUnary outputBranchRead
  have outputCert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont witness operation output ∧ Cont output continuation outputRead)
          (fun row : BHist => hsame row outputRead ∧ PkgSig bundle outputRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead
        ⟨hsame_refl outputRead, outputReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨witnessOperationOutput, outputContinuationRead⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, outputReadPkg⟩
  }
  have branchCert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont output branch branchRead ∧ Cont branch transport continuation)
          (fun row : BHist => hsame row branchRead ∧ PkgSig bundle branchRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead
        ⟨hsame_refl branchRead, branchReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨outputBranchRead, branchTransportContinuation⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, branchReadPkg⟩
  }
  exact ⟨outputCert, branchCert, outputReadUnary, branchReadUnary, provenancePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
