import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_provenance_stability [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert
      targetActive activeBlocking blockingExport exportProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target -> UnaryHistory active -> UnaryHistory retired ->
      UnaryHistory blocking -> UnaryHistory exportRow -> UnaryHistory replay ->
        Cont target active targetActive -> Cont active blocking activeBlocking ->
          Cont blocking exportRow blockingExport -> Cont exportRow replay exportProvenance ->
            PkgSig bundle provenance pkg -> hsame provenance exportProvenance ->
              activeReadingGateFields
                (ActiveReadingGateUp.mk target active retired blocking exportRow transport replay
                  provenance nameCert) =
                  [target, active, retired, blocking, exportRow, transport, replay, provenance,
                    nameCert] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row target ∨ hsame row active ∨ hsame row retired ∨
                      hsame row blocking ∨ hsame row exportRow ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row nameCert)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont target active targetActive ∧
                      Cont active blocking activeBlocking ∧
                        Cont blocking exportRow blockingExport ∧
                          Cont exportRow replay exportProvenance ∧
                            PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory provenance := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro targetUnary activeUnary retiredUnary blockingUnary exportUnary replayUnary
    targetActiveRoute activeBlockingRoute blockingExportRoute exportReplayRoute provenancePkg
    sameProvenance
  have exportProvenanceUnary : UnaryHistory exportProvenance :=
    unary_cont_closed exportUnary replayUnary exportReplayRoute
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport exportProvenanceUnary (hsame_symm sameProvenance)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row target ∨ hsame row active ∨ hsame row retired ∨ hsame row blocking ∨
            hsame row exportRow ∨ hsame row replay ∨ hsame row provenance ∨
              hsame row nameCert)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont target active targetActive ∧
            Cont active blocking activeBlocking ∧ Cont blocking exportRow blockingExport ∧
              Cont exportRow replay exportProvenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, provenanceUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetActiveRoute, activeBlockingRoute, blockingExportRoute,
          exportReplayRoute, provenancePkg⟩
  }
  exact ⟨rfl, cert, provenanceUnary⟩

end BEDC.Derived.ActiveReadingGateUp
