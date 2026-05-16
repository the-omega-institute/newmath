import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_route_endpoint_exactness
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        PkgSig bundle terminal pkg ->
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory terminal ∧ Cont B S W ∧
              Cont W D R ∧ Cont R E terminal ∧ hsame terminal C ∧ hsame N E ∧
                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetSchedule, windowDyadic,
    carrierTerminal, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have sameTerminal : hsame terminal C :=
    cont_deterministic terminalRoute carrierTerminal
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryTerminal, budgetSchedule,
      windowDyadic, terminalRoute, sameTerminal, sameName, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
