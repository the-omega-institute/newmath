import BEDC.Derived.ActiveReadingGateUp.LedgerNonescape

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_registry_consumer_coverage [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert ledgerRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target →
      UnaryHistory active →
        UnaryHistory retired →
          UnaryHistory blocking →
            UnaryHistory exportRow →
              UnaryHistory transport →
                UnaryHistory replay →
                  Cont target active blocking →
                    Cont blocking exportRow ledgerRead →
                      Cont ledgerRead replay provenance →
                        PkgSig bundle provenance pkg →
                          hsame provenance publicRead →
                            hsame publicRead nameCert →
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row target ∨ hsame row active ∨
                                      hsame row retired ∨ hsame row blocking ∨
                                        hsame row exportRow ∨ hsame row ledgerRead ∨
                                          hsame row publicRead ∨ hsame row transport ∨
                                            hsame row replay ∨ hsame row provenance ∨
                                              hsame row nameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont target active blocking ∧
                                      Cont blocking exportRow ledgerRead ∧
                                        Cont ledgerRead replay provenance ∧
                                          PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory retired ∧ UnaryHistory ledgerRead ∧
                                  UnaryHistory publicRead ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: ActiveReadingGateUp BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro _targetUnary _activeUnary retiredUnary blockingUnary exportUnary _transportUnary
    replayUnary targetActiveBlocking blockingExportLedger ledgerReplayProvenance provenancePkg
    provenancePublic publicName
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed blockingUnary exportUnary blockingExportLedger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary replayUnary ledgerReplayProvenance
  have publicUnary : UnaryHistory publicRead :=
    unary_transport provenanceUnary provenancePublic
  have nameUnary : UnaryHistory nameCert :=
    unary_transport publicUnary publicName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row retired ∨
              hsame row blocking ∨ hsame row exportRow ∨ hsame row ledgerRead ∨
                hsame row publicRead ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row nameCert)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetActiveBlocking, blockingExportLedger,
          ledgerReplayProvenance, provenancePkg⟩
  }
  exact ⟨cert, retiredUnary, ledgerUnary, publicUnary, nameUnary⟩

end BEDC.Derived.ActiveReadingGateUp
