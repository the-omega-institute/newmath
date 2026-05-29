import BEDC.Derived.MetaCICCriticalPathUp.L10NormalizationDischargeBudget

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealCompletionSNBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regRead realSeal socketRead snRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule provenance regRead →
            Cont regRead localName realSeal →
              Cont handoff obstruction socketRead →
                Cont strongNorm normalForm snRead →
                  PkgSig bundle realSeal pkg →
                    PkgSig bundle socketRead pkg →
                      PkgSig bundle snRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                                hsame row regRead ∨ hsame row realSeal ∨
                                  hsame row socketRead ∨ hsame row snRead)
                            (fun row : BHist => UnaryHistory row)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
                            hsame ∧
                          UnaryHistory realSeal ∧ UnaryHistory socketRead ∧
                            UnaryHistory snRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleProvenanceRead
    readLocalNameSeal handoffObstructionSocket strongNormNormalFormSnRead realSealPkg
    socketReadPkg snReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed streamScheduleUnary provenanceUnary scheduleProvenanceRead
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary localNameUnary readLocalNameSeal
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have snReadUnary : UnaryHistory snRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormSnRead
  have sourceBudget :
      (fun row : BHist =>
        hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regRead ∨
          hsame row realSeal ∨ hsame row socketRead ∨ hsame row snRead) dyadicBudget := by
    exact Or.inl (hsame_refl dyadicBudget)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regRead ∨
              hsame row realSeal ∨ hsame row socketRead ∨ hsame row snRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
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
                | inl sourceRead =>
                    exact Or.inr (Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sourceRead)))
                | inr rest =>
                    cases rest with
                    | inl sourceSeal =>
                        exact Or.inr (Or.inr (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sourceSeal))))
                    | inr rest =>
                        cases rest with
                        | inl sourceSocket =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sourceSocket)))))
                        | inr sourceSn =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sourceSn)))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sourceBudget =>
          exact unary_transport dyadicBudgetUnary (hsame_symm sourceBudget)
      | inr rest =>
          cases rest with
          | inl sourceSchedule =>
              exact unary_transport streamScheduleUnary (hsame_symm sourceSchedule)
          | inr rest =>
              cases rest with
              | inl sourceRead =>
                  exact unary_transport regReadUnary (hsame_symm sourceRead)
              | inr rest =>
                  cases rest with
                  | inl sourceSeal =>
                      exact unary_transport realSealUnary (hsame_symm sourceSeal)
                  | inr rest =>
                      cases rest with
                      | inl sourceSocket =>
                          exact unary_transport socketReadUnary (hsame_symm sourceSocket)
                      | inr sourceSn =>
                          exact unary_transport snReadUnary (hsame_symm sourceSn)
    ledger_sound := by
      intro _row source
      cases source with
      | inl _sourceBudget =>
          exact Or.inl provenancePkg
      | inr rest =>
          cases rest with
          | inl _sourceSchedule =>
              exact Or.inl provenancePkg
          | inr rest =>
              cases rest with
              | inl _sourceRead =>
                  exact Or.inl provenancePkg
              | inr rest =>
                  cases rest with
                  | inl sourceSeal =>
                      cases sourceSeal
                      exact Or.inr realSealPkg
                  | inr rest =>
                      cases rest with
                      | inl sourceSocket =>
                          cases sourceSocket
                          exact Or.inr socketReadPkg
                      | inr sourceSn =>
                          cases sourceSn
                          exact Or.inr snReadPkg
  }
  exact ⟨cert, realSealUnary, socketReadUnary, snReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
