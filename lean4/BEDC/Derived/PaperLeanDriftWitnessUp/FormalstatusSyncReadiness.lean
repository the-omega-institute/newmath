import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_formalstatus_sync_readiness [AskSetup] [PackageSetup]
    {M A L I R H C P N markerRead verdictRead statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont M A markerRead ->
        Cont markerRead R verdictRead ->
          Cont verdictRead P statusRead ->
            PkgSig bundle statusRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                      hsame row R ∨ hsame row statusRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M A markerRead ∧
                      Cont markerRead R verdictRead ∧
                        Cont verdictRead P statusRead ∧ PkgSig bundle statusRead pkg)
                  hsame ∧
                UnaryHistory markerRead ∧ UnaryHistory verdictRead ∧
                  UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier markerRoute verdictRoute statusRoute statusPkg
  obtain ⟨mUnary, aUnary, _lUnary, _iUnary, rUnary, _hUnary, _cUnary, pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have markerUnary : UnaryHistory markerRead :=
    unary_cont_closed mUnary aUnary markerRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed markerUnary rUnary verdictRoute
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed verdictUnary pUnary statusRoute
  have sourceAtStatus :
      (fun row : BHist => hsame row statusRead ∧ UnaryHistory row) statusRead :=
    ⟨hsame_refl statusRead, statusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row statusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M A markerRead ∧
              Cont markerRead R verdictRead ∧ Cont verdictRead P statusRead ∧
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
      exact ⟨source.right, markerRoute, verdictRoute, statusRoute, statusPkg⟩
  }
  exact ⟨cert, markerUnary, verdictUnary, statusUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
