import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_status_consumer_exactness [AskSetup] [PackageSetup]
    {M A L I R H C P N nameRead inventoryRead exactVerdict statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont A L nameRead ->
        Cont nameRead I inventoryRead ->
          Cont inventoryRead R exactVerdict ->
            Cont exactVerdict H statusRead ->
              PkgSig bundle statusRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row L ∨ hsame row I ∨ hsame row R ∨
                        hsame row H ∨ hsame row statusRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A L nameRead ∧
                        Cont nameRead I inventoryRead ∧
                          Cont inventoryRead R exactVerdict ∧
                            Cont exactVerdict H statusRead ∧
                              PkgSig bundle statusRead pkg)
                    hsame ∧
                  UnaryHistory nameRead ∧ UnaryHistory inventoryRead ∧
                    UnaryHistory exactVerdict ∧ UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier nameRoute inventoryRoute exactRoute statusRoute statusPkg
  obtain ⟨_mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed aUnary lUnary nameRoute
  have inventoryUnary : UnaryHistory inventoryRead :=
    unary_cont_closed nameUnary iUnary inventoryRoute
  have exactUnary : UnaryHistory exactVerdict :=
    unary_cont_closed inventoryUnary rUnary exactRoute
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed exactUnary hUnary statusRoute
  have sourceAtStatus :
      (fun row : BHist => hsame row statusRead ∧ UnaryHistory row) statusRead :=
    ⟨hsame_refl statusRead, statusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row L ∨ hsame row I ∨ hsame row R ∨
              hsame row H ∨ hsame row statusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L nameRead ∧ Cont nameRead I inventoryRead ∧
              Cont inventoryRead R exactVerdict ∧ Cont exactVerdict H statusRead ∧
                PkgSig bundle statusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro statusRead sourceAtStatus
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
      exact
        ⟨source.right, nameRoute, inventoryRoute, exactRoute, statusRoute,
          statusPkg⟩
  }
  exact ⟨cert, nameUnary, inventoryUnary, exactUnary, statusUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
