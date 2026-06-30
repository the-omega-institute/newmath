import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_bridge_ready_dependency_surface [AskSetup] [PackageSetup]
    {M A L I R H C P N bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont R C bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                  hsame row R ∨ hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont R C bridgeRead ∧ PkgSig bundle bridgeRead pkg)
              hsame ∧
            UnaryHistory bridgeRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier bridgeRoute bridgePkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed rUnary cUnary bridgeRoute
  have sourceAtBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R C bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
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
      exact ⟨source.right, bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary, namePkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
