import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_lean_inventory_hit_exhaustion [AskSetup] [PackageSetup]
    {M A L I R H C P N inventoryHit duplicateRefusal exactRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont A I inventoryHit ->
        Cont L R duplicateRefusal ->
          Cont inventoryHit R exactRead ->
            Cont duplicateRefusal H refusalRead ->
              PkgSig bundle exactRead pkg ->
                PkgSig bundle refusalRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row A ∨ hsame row I ∨ hsame row L ∨ hsame row R ∨
                          hsame row exactRead ∨ hsame row refusalRead)
                      (fun row : BHist =>
                        PkgSig bundle exactRead pkg ∧ PkgSig bundle refusalRead pkg ∧
                          hsame row exactRead)
                      hsame ∧
                    UnaryHistory inventoryHit ∧ UnaryHistory duplicateRefusal ∧
                      UnaryHistory exactRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier inventoryRoute duplicateRoute exactRoute refusalRoute exactPkg refusalPkg
  obtain ⟨_mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, _namePkg⟩ :=
    carrier
  have inventoryUnary : UnaryHistory inventoryHit :=
    unary_cont_closed aUnary iUnary inventoryRoute
  have duplicateUnary : UnaryHistory duplicateRefusal :=
    unary_cont_closed lUnary rUnary duplicateRoute
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed inventoryUnary rUnary exactRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed duplicateUnary hUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row I ∨ hsame row L ∨ hsame row R ∨
              hsame row exactRead ∨ hsame row refusalRead)
          (fun row : BHist =>
            PkgSig bundle exactRead pkg ∧ PkgSig bundle refusalRead pkg ∧
              hsame row exactRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exactRead ⟨hsame_refl exactRead, exactUnary⟩
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
      exact ⟨exactPkg, refusalPkg, source.left⟩
  }
  exact ⟨cert, inventoryUnary, duplicateUnary, exactUnary, refusalUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
