import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_public_export_route [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont R H verdictRead ->
        Cont verdictRead C replayRead ->
          Cont replayRead P publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                      hsame row R ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R H verdictRead ∧
                      Cont verdictRead C replayRead ∧ Cont replayRead P publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory verdictRead ∧ UnaryHistory replayRead ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier verdictRoute replayRoute publicRoute publicPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, hUnary, cUnary, pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed verdictUnary cUnary replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary pUnary publicRoute
  have sourceAtPublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R H verdictRead ∧
              Cont verdictRead C replayRead ∧ Cont replayRead P publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, verdictRoute, replayRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, verdictUnary, replayUnary, publicUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
