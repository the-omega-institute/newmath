import BEDC.Derived.ActiveReadingGateUp.LedgerNonescape

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_current_retired_disjointness [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert ledgerRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target →
      UnaryHistory active →
        UnaryHistory retired →
          UnaryHistory blocking →
            UnaryHistory exportRow →
              UnaryHistory replay →
                Cont target active blocking →
                  Cont blocking exportRow ledgerRead →
                    Cont ledgerRead replay provenance →
                      PkgSig bundle provenance pkg →
                        hsame provenance publicRead →
                          hsame publicRead nameCert →
                            activeReadingGateFields
                                (ActiveReadingGateUp.mk target active retired blocking
                                  exportRow transport replay provenance nameCert) =
                              [target, active, retired, blocking, exportRow, transport, replay,
                                provenance, nameCert] ∧
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row target ∨ hsame row active ∨
                                      hsame row blocking ∨ hsame row exportRow ∨
                                        hsame row ledgerRead ∨ hsame row publicRead ∨
                                          hsame row replay ∨ hsame row provenance ∨
                                            hsame row nameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont target active blocking ∧
                                      Cont blocking exportRow ledgerRead ∧
                                        Cont ledgerRead replay provenance ∧
                                          PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory active ∧ UnaryHistory retired ∧
                                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ActiveReadingGateUp BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro _targetUnary activeUnary retiredUnary blockingUnary exportUnary replayUnary
    targetActiveBlocking blockingExportLedger ledgerReplayProvenance provenancePkg
    provenancePublic _publicName
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed blockingUnary exportUnary blockingExportLedger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary replayUnary ledgerReplayProvenance
  have publicUnary : UnaryHistory publicRead :=
    unary_transport provenanceUnary provenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row blocking ∨
              hsame row exportRow ∨ hsame row ledgerRead ∨ hsame row publicRead ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active blocking ∧
              Cont blocking exportRow ledgerRead ∧ Cont ledgerRead replay provenance ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, targetActiveBlocking, blockingExportLedger,
          ledgerReplayProvenance, provenancePkg⟩
  }
  exact ⟨rfl, cert, activeUnary, retiredUnary, publicUnary⟩

end BEDC.Derived.ActiveReadingGateUp
