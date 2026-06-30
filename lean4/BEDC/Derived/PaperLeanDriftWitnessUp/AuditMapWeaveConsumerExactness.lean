import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_auditmap_weave_consumer_exactness [AskSetup] [PackageSetup]
    {M A L I R H C P N markerRead inventoryRead verdictRead dependencyRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont M A markerRead ->
        Cont markerRead I inventoryRead ->
          Cont inventoryRead R verdictRead ->
            Cont verdictRead C dependencyRead ->
              Cont dependencyRead H handoffRead ->
                PkgSig bundle handoffRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                          hsame row R ∨ hsame row dependencyRead ∨ hsame row handoffRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle handoffRead pkg)
                      hsame ∧
                    UnaryHistory markerRead ∧ UnaryHistory inventoryRead ∧
                      UnaryHistory verdictRead ∧ UnaryHistory dependencyRead ∧
                        UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier markerRoute inventoryRoute verdictRoute dependencyRoute handoffRoute
    handoffPkg
  obtain ⟨mUnary, aUnary, _lUnary, iUnary, rUnary, hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have markerUnary : UnaryHistory markerRead :=
    unary_cont_closed mUnary aUnary markerRoute
  have inventoryUnary : UnaryHistory inventoryRead :=
    unary_cont_closed markerUnary iUnary inventoryRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed inventoryUnary rUnary verdictRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed verdictUnary cUnary dependencyRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed dependencyUnary hUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row dependencyRead ∨ hsame row handoffRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact ⟨source.right, handoffPkg⟩
  }
  exact
    ⟨cert, markerUnary, inventoryUnary, verdictUnary, dependencyUnary, handoffUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
