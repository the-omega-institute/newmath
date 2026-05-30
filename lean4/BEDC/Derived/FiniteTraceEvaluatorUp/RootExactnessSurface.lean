import BEDC.Derived.FiniteTraceEvaluatorUp.NameCertObligations

namespace BEDC.Derived.FiniteTraceEvaluatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTraceEvaluatorCheckpointLedgerCut [AskSetup] [PackageSetup]
    {input trace accepted validation transport replay provenance nameRow checkpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTraceEvaluatorCarrier input trace accepted validation transport replay provenance
        nameRow bundle pkg →
      Cont validation replay checkpointRead →
        PkgSig bundle checkpointRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row checkpointRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row validation ∨ hsame row replay ∨ Cont validation replay checkpointRead)
              (fun row : BHist => PkgSig bundle checkpointRead pkg ∧ hsame row checkpointRead)
              hsame ∧
            UnaryHistory checkpointRead ∧ PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier validationReplayCheckpoint checkpointPkg
  obtain ⟨_inputUnary, _traceUnary, _acceptedUnary, validationUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameRowUnary, _inputTraceReplay,
    _replayAcceptedNameRow, _acceptedValidationProvenance, _transportSame,
    _provenancePkg⟩ := carrier
  have checkpointUnary : UnaryHistory checkpointRead :=
    unary_cont_closed validationUnary replayUnary validationReplayCheckpoint
  have sourceWitness :
      (fun row : BHist => hsame row checkpointRead ∧ UnaryHistory row) checkpointRead := by
    exact ⟨hsame_refl checkpointRead, checkpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row checkpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row validation ∨ hsame row replay ∨ Cont validation replay checkpointRead)
          (fun row : BHist => PkgSig bundle checkpointRead pkg ∧ hsame row checkpointRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro checkpointRead sourceWitness
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr validationReplayCheckpoint)
    ledger_sound := by
      intro _row source
      exact ⟨checkpointPkg, source.left⟩
  }
  exact ⟨cert, checkpointUnary, checkpointPkg⟩

end BEDC.Derived.FiniteTraceEvaluatorUp
