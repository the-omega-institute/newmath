import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_operation_landing_exactness [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      outputRead branchBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation outputRead →
        Cont outputRead branch branchBoundary →
          PkgSig bundle outputRead pkg →
            PkgSig bundle branchBoundary pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row outputRead ∨ hsame row branchBoundary)
                  (fun _row : BHist =>
                    Cont output continuation outputRead ∧
                      Cont outputRead branch branchBoundary)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle outputRead pkg ∨ PkgSig bundle branchBoundary pkg))
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory branchBoundary ∧
                  Cont witness operation output ∧ Cont output continuation outputRead ∧
                    Cont outputRead branch branchBoundary ∧
                      Cont branch transport continuation ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle outputRead pkg ∧
                          PkgSig bundle branchBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier outputContinuationRead outputReadBranchBoundary outputReadPkg
    branchBoundaryPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationRead
  have branchBoundaryUnary : UnaryHistory branchBoundary :=
    unary_cont_closed outputReadUnary branchUnary outputReadBranchBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∨ hsame row branchBoundary)
          (fun _row : BHist =>
            Cont output continuation outputRead ∧ Cont outputRead branch branchBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle outputRead pkg ∨ PkgSig bundle branchBoundary pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead (Or.inl (hsame_refl outputRead))
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
        cases source with
        | inl sameOutput =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameOutput)
        | inr sameBoundary =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameBoundary)
    }
    pattern_sound := by
      intro _row _source
      exact ⟨outputContinuationRead, outputReadBranchBoundary⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameOutput =>
          exact
            ⟨unary_transport outputReadUnary (hsame_symm sameOutput),
              Or.inl outputReadPkg⟩
      | inr sameBoundary =>
          exact
            ⟨unary_transport branchBoundaryUnary (hsame_symm sameBoundary),
              Or.inr branchBoundaryPkg⟩
  }
  exact
    ⟨cert, outputReadUnary, branchBoundaryUnary, witnessOperationOutput,
      outputContinuationRead, outputReadBranchBoundary, branchTransportContinuation,
      provenancePkg, outputReadPkg, branchBoundaryPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
