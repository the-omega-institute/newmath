import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFourSourceOwnerNoncollapse [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal dependencyDiamond ownerBudget ownerSchedule
      ownerReadback ownerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont handoff continuation dependencyDiamond ->
        Cont dyadic stream ownerBudget ->
          Cont stream regseq ownerSchedule ->
            Cont regseq realSeal ownerReadback ->
              Cont realSeal dependencyDiamond ownerSeal ->
                PkgSig bundle dependencyDiamond pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row ownerBudget ∨ hsame row ownerSchedule ∨
                          hsame row ownerReadback ∨ hsame row ownerSeal)
                      (fun row : BHist =>
                        (hsame row ownerBudget ∨ hsame row ownerSchedule ∨
                          hsame row ownerReadback ∨ hsame row ownerSeal) ∨
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal ∨ hsame row dependencyDiamond)
                      (fun row : BHist =>
                        PkgSig bundle dependencyDiamond pkg ∧
                          (hsame row ownerBudget ∨ hsame row ownerSchedule ∨
                            hsame row ownerReadback ∨ hsame row ownerSeal))
                      hsame ∧
                    UnaryHistory ownerBudget ∧ UnaryHistory ownerSchedule ∧
                      UnaryHistory ownerReadback ∧ UnaryHistory ownerSeal := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger handoffContinuationDiamond dyadicStreamOwner streamRegseqOwner
    regseqRealSealOwner realSealDiamondOwner dependencyDiamondPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have dependencyDiamondUnary : UnaryHistory dependencyDiamond :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationDiamond
  have ownerBudgetUnary : UnaryHistory ownerBudget :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamOwner
  have ownerScheduleUnary : UnaryHistory ownerSchedule :=
    unary_cont_closed streamUnary regseqUnary streamRegseqOwner
  have ownerReadbackUnary : UnaryHistory ownerReadback :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealOwner
  have ownerSealUnary : UnaryHistory ownerSeal :=
    unary_cont_closed realSealUnary dependencyDiamondUnary realSealDiamondOwner
  have sourceBudget :
      (fun row : BHist =>
        hsame row ownerBudget ∨ hsame row ownerSchedule ∨
          hsame row ownerReadback ∨ hsame row ownerSeal) ownerBudget := by
    exact Or.inl (hsame_refl ownerBudget)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ownerBudget ∨ hsame row ownerSchedule ∨
              hsame row ownerReadback ∨ hsame row ownerSeal)
          (fun row : BHist =>
            (hsame row ownerBudget ∨ hsame row ownerSchedule ∨
              hsame row ownerReadback ∨ hsame row ownerSeal) ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row dependencyDiamond)
          (fun row : BHist =>
            PkgSig bundle dependencyDiamond pkg ∧
              (hsame row ownerBudget ∨ hsame row ownerSchedule ∨
                hsame row ownerReadback ∨ hsame row ownerSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ownerBudget sourceBudget
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
        | inl sourceBudget =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sourceBudget)
        | inr rest =>
            cases rest with
            | inl sourceSchedule =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sourceSchedule))
            | inr rest =>
                cases rest with
                | inl sourceReadback =>
                    exact
                      Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sourceReadback)))
                | inr sourceSeal =>
                    exact
                      Or.inr (Or.inr (Or.inr
                        (hsame_trans (hsame_symm sameRows) sourceSeal)))
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source
    ledger_sound := by
      intro _row source
      exact ⟨dependencyDiamondPkg, source⟩
  }
  exact ⟨cert, ownerBudgetUnary, ownerScheduleUnary, ownerReadbackUnary, ownerSealUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
