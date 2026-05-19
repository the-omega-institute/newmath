import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_vision_concretization [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      localOutput obstructionRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation localOutput →
        Cont branch transport obstructionRead →
          Cont localOutput obstructionRead exportRead →
            PkgSig bundle exportRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row localOutput ∨ hsame row obstructionRead ∨ hsame row exportRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory localOutput ∧ UnaryHistory obstructionRead ∧
                  UnaryHistory exportRead ∧ Cont witness operation output := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier outputContinuationLocal branchTransportObstruction localObstructionExport
    exportReadPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have localOutputUnary : UnaryHistory localOutput :=
    unary_cont_closed outputUnary continuationUnary outputContinuationLocal
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed branchUnary transportUnary branchTransportObstruction
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed localOutputUnary obstructionReadUnary localObstructionExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localOutput ∨ hsame row obstructionRead ∨ hsame row exportRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localOutput (Or.inl (hsame_refl localOutput))
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
        | inl sameLocal =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocal)
        | inr rest =>
            cases rest with
            | inl sameObstruction =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction))
            | inr sameExport =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameExport))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameLocal =>
          exact unary_transport localOutputUnary (hsame_symm sameLocal)
      | inr rest =>
          cases rest with
          | inl sameObstruction =>
              exact unary_transport obstructionReadUnary (hsame_symm sameObstruction)
          | inr sameExport =>
              exact unary_transport exportReadUnary (hsame_symm sameExport)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, exportReadPkg⟩
  }
  exact
    ⟨cert, localOutputUnary, obstructionReadUnary, exportReadUnary, witnessOperationOutput⟩

end BEDC.Derived.AnalyticContinuationSocketUp
