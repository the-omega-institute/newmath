import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FiniteObservationBudgetSelectorCarrier_terminal_route_no_branching
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminalA terminalB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont B S W ->
        Cont W D R ->
          Cont R E terminalA ->
            Cont R E terminalB ->
              PkgSig bundle terminalA pkg ->
                PkgSig bundle terminalB pkg ->
                  hsame terminalA terminalB ∧ Cont B S W ∧ Cont W D R ∧
                    Cont R E terminalA ∧ Cont R E terminalB ∧ hsame N E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier budgetWindow windowRegular terminalRouteA terminalRouteB _terminalPkgA
    _terminalPkgB
  obtain ⟨_unaryB, _unaryS, _unaryD, _unaryE, _unaryH, _carrierBudget,
    _carrierWindow, _carrierTerminal, sameName⟩ := carrier
  have sameTerminal : hsame terminalA terminalB :=
    cont_deterministic terminalRouteA terminalRouteB
  exact
    ⟨sameTerminal, budgetWindow, windowRegular, terminalRouteA, terminalRouteB, sameName⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
