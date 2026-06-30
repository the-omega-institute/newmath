import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_duplicate_ledger_readiness [AskSetup] [PackageSetup]
    {M A L I R H C P N duplicateRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont L R duplicateRead →
        Cont duplicateRead H refusalRead →
          PkgSig bundle refusalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row L ∨ hsame row R ∨ hsame row H ∨
                    hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L R duplicateRead ∧
                    Cont duplicateRead H refusalRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle refusalRead pkg)
                hsame ∧
              UnaryHistory duplicateRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier duplicateRoute refusalRoute refusalPkg
  obtain ⟨_mUnary, _aUnary, lUnary, _iUnary, rUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have duplicateUnary : UnaryHistory duplicateRead :=
    unary_cont_closed lUnary rUnary duplicateRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed duplicateUnary hUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row L ∨ hsame row R ∨ hsame row H ∨
              hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L R duplicateRead ∧
              Cont duplicateRead H refusalRead ∧ PkgSig bundle N pkg ∧
                PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, duplicateRoute, refusalRoute, namePkg, refusalPkg⟩
  }
  exact ⟨cert, duplicateUnary, refusalUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
