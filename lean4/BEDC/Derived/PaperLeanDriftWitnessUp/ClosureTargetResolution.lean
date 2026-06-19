import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_closure_target_resolution [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        Cont verdictRead P closureRead →
          PkgSig bundle closureRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row closureRead)
                (fun row : BHist => PkgSig bundle closureRead pkg ∧ hsame row closureRead)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
                UnaryHistory R ∧ UnaryHistory verdictRead ∧ UnaryHistory closureRead ∧
                  Cont L I R ∧ Cont R H verdictRead ∧ Cont verdictRead P closureRead ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle closureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier verdictRoute closureRoute closurePkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, _cUnary, pUnary, _nUnary,
    _markerNameLedger, ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed verdictUnary pUnary closureRoute
  have sourceAtClosure : hsame closureRead closureRead ∧ UnaryHistory closureRead :=
    ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row closureRead)
          (fun row : BHist => PkgSig bundle closureRead pkg ∧ hsame row closureRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceAtClosure
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
      exact ⟨closurePkg, source.left⟩
  }
  exact
    ⟨cert, mUnary, aUnary, lUnary, iUnary, rUnary, verdictUnary, closureUnary,
      ledgerInventoryVerdict, verdictRoute, closureRoute, namePkg, closurePkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
