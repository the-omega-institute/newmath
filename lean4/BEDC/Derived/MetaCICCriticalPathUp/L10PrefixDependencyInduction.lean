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

theorem MetaCICCriticalPathL10PrefixDependencyInduction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal budgetPrefix schedulePrefix readbackPrefix
      sealPrefix : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream budgetPrefix →
        Cont budgetPrefix regseq schedulePrefix →
          Cont schedulePrefix realSeal readbackPrefix →
            Cont readbackPrefix handoff sealPrefix →
              PkgSig bundle sealPrefix pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
                        hsame row readbackPrefix ∨ hsame row sealPrefix)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row budgetPrefix ∨
                          hsame row schedulePrefix ∨ hsame row readbackPrefix ∨
                            hsame row sealPrefix)
                    (fun row : BHist =>
                      PkgSig bundle sealPrefix pkg ∧
                        (hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
                          hsame row readbackPrefix ∨ hsame row sealPrefix))
                    hsame ∧
                  UnaryHistory budgetPrefix ∧ UnaryHistory schedulePrefix ∧
                    UnaryHistory readbackPrefix ∧ UnaryHistory sealPrefix := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamBudget budgetRegseqSchedule scheduleRealSealReadback
    readbackHandoffSeal sealPrefixPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamBudget
  have schedulePrefixUnary : UnaryHistory schedulePrefix :=
    unary_cont_closed budgetPrefixUnary regseqUnary budgetRegseqSchedule
  have readbackPrefixUnary : UnaryHistory readbackPrefix :=
    unary_cont_closed schedulePrefixUnary realSealUnary scheduleRealSealReadback
  have sealPrefixUnary : UnaryHistory sealPrefix :=
    unary_cont_closed readbackPrefixUnary handoffUnary readbackHandoffSeal
  have sourceBudget :
      (fun row : BHist =>
        hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
          hsame row readbackPrefix ∨ hsame row sealPrefix) budgetPrefix := by
    exact Or.inl (hsame_refl budgetPrefix)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
              hsame row readbackPrefix ∨ hsame row sealPrefix)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
                hsame row readbackPrefix ∨ hsame row sealPrefix)
          (fun row : BHist =>
            PkgSig bundle sealPrefix pkg ∧
              (hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
                hsame row readbackPrefix ∨ hsame row sealPrefix))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetPrefix sourceBudget
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
      cases source with
      | inl sourceBudget =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceBudget))))
      | inr rest =>
          cases rest with
          | inl sourceSchedule =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceSchedule)))))
          | inr rest =>
              cases rest with
              | inl sourceReadback =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl sourceReadback))))))
              | inr sourceSeal =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr sourceSeal))))))
    ledger_sound := by
      intro _row source
      exact ⟨sealPrefixPkg, source⟩
  }
  exact
    ⟨cert, budgetPrefixUnary, schedulePrefixUnary, readbackPrefixUnary, sealPrefixUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
