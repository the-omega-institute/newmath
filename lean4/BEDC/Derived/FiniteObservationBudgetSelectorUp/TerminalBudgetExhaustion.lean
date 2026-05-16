import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_budget_exhaustion
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        PkgSig bundle terminal pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row terminal ∧ Cont B S W ∧ Cont W D R ∧ Cont R E terminal)
            (fun _row : BHist =>
              Cont B S W ∧ Cont W D R ∧ Cont R E terminal ∧
                hsame N E ∧ PkgSig bundle terminal pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier terminalRoute terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, windowRoute,
    _sealRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminal ⟨hsame_refl terminal, unaryTerminal⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, budgetRoute, windowRoute, terminalRoute⟩
    ledger_sound := by
      intro _row _source
      exact ⟨budgetRoute, windowRoute, terminalRoute, sameName, terminalPkg⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
