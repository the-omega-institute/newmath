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

theorem MetaCICCriticalPathL10EntryBudgetSynchronization [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont route localName dyadicBudget ->
        Cont dyadicBudget route streamSchedule ->
          Cont streamSchedule normalForm regReadback ->
            Cont regReadback provenance realSeal ->
              PkgSig bundle realSeal pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                        hsame row regReadback ∨ hsame row realSeal)
                    (fun row : BHist =>
                      hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                        hsame row regReadback ∨ hsame row realSeal)
                    (fun row : BHist =>
                      PkgSig bundle realSeal pkg ∧
                        (hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                          hsame row regReadback ∨ hsame row realSeal))
                    hsame ∧
                  UnaryHistory dyadicBudget ∧ UnaryHistory streamSchedule ∧
                    UnaryHistory regReadback ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal realSealPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have sourceBudget :
      (fun row : BHist =>
        hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regReadback ∨
          hsame row realSeal) dyadicBudget := by
    exact Or.inl (hsame_refl dyadicBudget)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regReadback ∨
              hsame row realSeal)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regReadback ∨
              hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                hsame row regReadback ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadicBudget sourceBudget
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
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source⟩
  }
  exact
    ⟨cert, dyadicBudgetUnary, streamScheduleUnary, regReadbackUnary, realSealUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
