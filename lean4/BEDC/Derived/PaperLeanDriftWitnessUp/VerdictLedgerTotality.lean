import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_verdict_ledger_totality [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont L I verdictRead ->
        Cont verdictRead R ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row ledgerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L I verdictRead ∧
                    Cont verdictRead R ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                hsame ∧
              UnaryHistory verdictRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier verdictRoute ledgerRoute ledgerPkg
  obtain ⟨_mUnary, _aUnary, lUnary, iUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed lUnary iUnary verdictRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed verdictUnary rUnary ledgerRoute
  have sourceAtLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L I verdictRead ∧
              Cont verdictRead R ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
      exact ⟨source.right, verdictRoute, ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, verdictUnary, ledgerUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
