import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitnessUnresolvedMarkerRefusal [AskSetup] [PackageSetup]
    {M A L I R H C P N refusalRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H refusalRead →
        Cont refusalRead C consumerRead →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row H ∨ hsame row refusalRead ∨
                      hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L I R ∧ Cont R H refusalRead ∧
                    Cont refusalRead C consumerRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle consumerRead pkg)
                hsame ∧
              UnaryHistory refusalRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier refusalRoute consumerRoute consumerPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary hUnary refusalRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed refusalUnary cUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨ hsame row R ∨
              hsame row H ∨ hsame row refusalRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L I R ∧ Cont R H refusalRead ∧
              Cont refusalRead C consumerRead ∧ PkgSig bundle N pkg ∧
                PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerInventoryVerdict, refusalRoute, consumerRoute, namePkg,
        consumerPkg⟩
  }
  exact ⟨cert, refusalUnary, consumerUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
