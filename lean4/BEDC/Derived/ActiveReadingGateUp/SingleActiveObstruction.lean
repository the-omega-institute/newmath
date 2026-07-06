import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_single_active_obstruction [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert activeRead
      retiredRead blockedRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target ->
      UnaryHistory active ->
        UnaryHistory retired ->
          UnaryHistory blocking ->
            UnaryHistory exportRow ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont target active activeRead ->
                    Cont retired transport retiredRead ->
                      Cont activeRead blocking blockedRead ->
                        Cont blockedRead replay provenance ->
                          PkgSig bundle provenance pkg ->
                            hsame provenance nameCert ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row blockedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row active ∨ hsame row retired ∨
                                      hsame row blocking ∨ hsame row activeRead ∨
                                        hsame row retiredRead ∨ hsame row blockedRead ∨
                                          hsame row provenance ∨ hsame row nameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont target active activeRead ∧
                                      Cont retired transport retiredRead ∧
                                        Cont activeRead blocking blockedRead ∧
                                          Cont blockedRead replay provenance ∧
                                            PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory activeRead ∧ UnaryHistory retiredRead ∧
                                  UnaryHistory blockedRead ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro targetUnary activeUnary retiredUnary blockingUnary _exportUnary transportUnary
    replayUnary targetActive retiredTransport activeBlocking blockedReplay provenancePkg
    provenanceName
  have activeReadUnary : UnaryHistory activeRead :=
    unary_cont_closed targetUnary activeUnary targetActive
  have retiredReadUnary : UnaryHistory retiredRead :=
    unary_cont_closed retiredUnary transportUnary retiredTransport
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed activeReadUnary blockingUnary activeBlocking
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed blockedReadUnary replayUnary blockedReplay
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport provenanceUnary provenanceName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row blockedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row active ∨ hsame row retired ∨ hsame row blocking ∨
              hsame row activeRead ∨ hsame row retiredRead ∨ hsame row blockedRead ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active activeRead ∧
              Cont retired transport retiredRead ∧ Cont activeRead blocking blockedRead ∧
                Cont blockedRead replay provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro blockedRead ⟨hsame_refl blockedRead, blockedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetActive, retiredTransport, activeBlocking, blockedReplay,
          provenancePkg⟩
  }
  exact ⟨cert, activeReadUnary, retiredReadUnary, blockedReadUnary, nameCertUnary⟩

end BEDC.Derived.ActiveReadingGateUp
