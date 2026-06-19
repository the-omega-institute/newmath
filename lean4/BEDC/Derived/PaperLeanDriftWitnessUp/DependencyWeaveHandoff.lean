import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_dependency_weave_handoff [AskSetup] [PackageSetup]
    {M A L I R H C P N dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont C P dependencyRead →
        PkgSig bundle dependencyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨ hsame row R ∨
                  hsame row dependencyRead)
              (fun row : BHist => hsame row dependencyRead ∧ PkgSig bundle dependencyRead pkg)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
              UnaryHistory R ∧ UnaryHistory C ∧ UnaryHistory P ∧
                UnaryHistory dependencyRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier dependencyRoute dependencyPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, _hUnary, cUnary, pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed cUnary pUnary dependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨ hsame row R ∨
              hsame row dependencyRead)
          (fun row : BHist => hsame row dependencyRead ∧ PkgSig bundle dependencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead ⟨hsame_refl dependencyRead, dependencyUnary⟩
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
      exact ⟨source.left, dependencyPkg⟩
  }
  exact
    ⟨cert, mUnary, aUnary, lUnary, iUnary, rUnary, cUnary, pUnary, dependencyUnary,
      namePkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
