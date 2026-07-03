import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_single_export_route [AskSetup] [PackageSetup]
    {target active blocking exportRow replay provenance nameCert exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target ->
      UnaryHistory active ->
        UnaryHistory blocking ->
          UnaryHistory exportRow ->
            UnaryHistory replay ->
              Cont target active blocking ->
                Cont blocking exportRow exportRead ->
                  Cont exportRead replay provenance ->
                    PkgSig bundle provenance pkg ->
                      hsame provenance nameCert ->
                        SemanticNameCert
                            (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row target ∨ hsame row active ∨ hsame row blocking ∨
                                hsame row exportRow ∨ hsame row exportRead ∨ hsame row replay ∨
                                  hsame row provenance ∨ hsame row nameCert)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont target active blocking ∧
                                Cont blocking exportRow exportRead ∧
                                  Cont exportRead replay provenance ∧
                                    PkgSig bundle provenance pkg)
                            hsame ∧
                          UnaryHistory exportRead ∧ UnaryHistory provenance ∧
                            UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro _targetUnary _activeUnary blockingUnary exportUnary replayUnary targetActive
    blockingExport exportReplay provenancePkg provenanceName
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed blockingUnary exportUnary blockingExport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed exportReadUnary replayUnary exportReplay
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport provenanceUnary provenanceName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row blocking ∨
              hsame row exportRow ∨ hsame row exportRead ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active blocking ∧
              Cont blocking exportRow exportRead ∧ Cont exportRead replay provenance ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetActive, blockingExport, exportReplay, provenancePkg⟩
  }
  exact ⟨cert, exportReadUnary, provenanceUnary, nameCertUnary⟩

end BEDC.Derived.ActiveReadingGateUp
