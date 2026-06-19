import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_duplicate_obstruction_route_preservation [AskSetup]
    [PackageSetup] {M A L I R H C P N duplicateRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont M L duplicateRead →
        Cont duplicateRead C obstructionRead →
          PkgSig bundle obstructionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row duplicateRead ∨ hsame row obstructionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M L duplicateRead ∧
                    Cont duplicateRead C obstructionRead ∧ PkgSig bundle obstructionRead pkg)
                hsame ∧
              UnaryHistory duplicateRead ∧ UnaryHistory obstructionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier duplicateRoute obstructionRoute obstructionPkg
  obtain ⟨mUnary, _aUnary, lUnary, _iUnary, _rUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have duplicateUnary : UnaryHistory duplicateRead :=
    unary_cont_closed mUnary lUnary duplicateRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed duplicateUnary cUnary obstructionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row duplicateRead ∨ hsame row obstructionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M L duplicateRead ∧
              Cont duplicateRead C obstructionRead ∧ PkgSig bundle obstructionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obstructionRead ⟨hsame_refl obstructionRead, obstructionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, duplicateRoute, obstructionRoute, obstructionPkg⟩
  }
  exact ⟨cert, duplicateUnary, obstructionUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
