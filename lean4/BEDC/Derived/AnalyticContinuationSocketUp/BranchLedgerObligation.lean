import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_branch_ledger_obligation [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      branchRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch branchRead →
        Cont branchRead transport ledgerRead →
          PkgSig bundle ledgerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row branch ∨ hsame row branchRead ∨ hsame row ledgerRead)
                (fun row : BHist => UnaryHistory row)
                (fun row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
                hsame ∧
              UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier outputBranchRead branchReadTransport _ledgerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed outputUnary branchUnary outputBranchRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed branchReadUnary transportUnary branchReadTransport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row branch ∨ hsame row branchRead ∨ hsame row ledgerRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branch (Or.inl (hsame_refl branch))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases source with
        | inl sameBranch =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBranch)
        | inr rest =>
            cases rest with
            | inl sameRead =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRead))
            | inr sameLedger =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameBranch =>
          exact unary_transport branchUnary (hsame_symm sameBranch)
      | inr rest =>
          cases rest with
          | inl sameRead =>
              exact unary_transport branchReadUnary (hsame_symm sameRead)
          | inr sameLedger =>
              exact unary_transport ledgerReadUnary (hsame_symm sameLedger)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, ledgerReadUnary⟩

end BEDC.Derived.AnalyticContinuationSocketUp
