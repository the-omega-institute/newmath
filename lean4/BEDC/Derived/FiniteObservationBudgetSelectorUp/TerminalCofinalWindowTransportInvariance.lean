import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FiniteObservationBudgetSelectorCarrier_terminal_cofinal_window_transport_invariance
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal0 terminal1 cofinal0 cofinal1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal0 ->
        Cont terminal0 H cofinal0 ->
          Cont R E terminal1 ->
            Cont terminal1 H cofinal1 ->
              PkgSig bundle cofinal0 pkg ->
                PkgSig bundle cofinal1 pkg ->
                  hsame terminal0 terminal1 ∧ hsame cofinal0 cofinal1 ∧
                    PkgSig bundle cofinal0 pkg ∧ PkgSig bundle cofinal1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier terminalRoute0 cofinalRoute0 terminalRoute1 cofinalRoute1 cofinalPkg0
    cofinalPkg1
  obtain ⟨_unaryB, _unaryS, _unaryD, _unaryE, _unaryH, _routeW, _routeR, _routeC,
    _sameName⟩ := carrier
  have sameTerminal : hsame terminal0 terminal1 :=
    cont_deterministic terminalRoute0 terminalRoute1
  have sameCofinal : hsame cofinal0 cofinal1 :=
    cont_respects_hsame sameTerminal (hsame_refl H) cofinalRoute0 cofinalRoute1
  exact ⟨sameTerminal, sameCofinal, cofinalPkg0, cofinalPkg1⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
