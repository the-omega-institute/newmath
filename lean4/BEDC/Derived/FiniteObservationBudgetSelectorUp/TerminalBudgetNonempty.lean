import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_budget_nonempty
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      PkgSig bundle C pkg ->
        Exists (fun terminal : BHist =>
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory terminal ∧ Cont B S W ∧
              Cont W D R ∧ Cont R E terminal ∧ hsame terminal C ∧ hsame N E ∧
                PkgSig bundle terminal pkg) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame
  intro carrier terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    terminalRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryR unaryE terminalRoute
  exact
    ⟨C, unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryC, budgetRoute,
      regularRoute, terminalRoute, hsame_refl C, sameName, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
