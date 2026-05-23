import BEDC.Derived.AnalyticContinuationSocketUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_overlap_to_zeta_handoff [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      zetaRead obstruction handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch zetaRead →
        Cont zetaRead transport obstruction →
          Cont obstruction name handoff →
            PkgSig bundle handoff pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row zetaRead ∨ hsame row obstruction ∨ hsame row handoff)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist =>
                    Cont output branch zetaRead ∧ Cont zetaRead transport obstruction ∧
                      Cont obstruction name handoff ∧ PkgSig bundle handoff pkg)
                  hsame ∧
                UnaryHistory zetaRead ∧ UnaryHistory obstruction ∧ UnaryHistory handoff ∧
                  Cont branch transport continuation ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputBranchZeta zetaTransportObstruction obstructionNameHandoff handoffPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_cont_closed outputUnary branchUnary outputBranchZeta
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed zetaReadUnary transportUnary zetaTransportObstruction
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed obstructionUnary nameUnary obstructionNameHandoff
  have sourceZeta :
      (fun row : BHist =>
        hsame row zetaRead ∨ hsame row obstruction ∨ hsame row handoff) zetaRead :=
    Or.inl (hsame_refl zetaRead)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row zetaRead ∨ hsame row obstruction ∨ hsame row handoff)
        (fun row : BHist => UnaryHistory row)
        (fun _row : BHist =>
          Cont output branch zetaRead ∧ Cont zetaRead transport obstruction ∧
            Cont obstruction name handoff ∧ PkgSig bundle handoff pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro zetaRead sourceZeta
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
        | inl sameZeta =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameZeta)
        | inr rest =>
            cases rest with
            | inl sameObstruction =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction))
            | inr sameHandoff =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameHandoff))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameZeta =>
          exact unary_transport zetaReadUnary (hsame_symm sameZeta)
      | inr rest =>
          cases rest with
          | inl sameObstruction =>
              exact unary_transport obstructionUnary (hsame_symm sameObstruction)
          | inr sameHandoff =>
              exact unary_transport handoffUnary (hsame_symm sameHandoff)
    ledger_sound := by
      intro _row _source
      exact ⟨outputBranchZeta, zetaTransportObstruction, obstructionNameHandoff, handoffPkg⟩
  }
  exact
    ⟨cert, zetaReadUnary, obstructionUnary, handoffUnary, branchTransportContinuation,
      provenancePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
