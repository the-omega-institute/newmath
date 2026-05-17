import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_cofinal_window_route_reflection
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont W D R →
        Cont R E routeRead →
          PkgSig bundle routeRead pkg →
            UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
              UnaryHistory routeRead ∧ Cont W D R ∧ Cont R E routeRead ∧
                hsame C routeRead ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier routeWindow routeTerminal routePkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeB, _carrierWindow,
    carrierTerminal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeB
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeWindow
  have unaryRouteRead : UnaryHistory routeRead :=
    unary_cont_closed unaryR unaryE routeTerminal
  have sameRoute : hsame C routeRead :=
    cont_deterministic carrierTerminal routeTerminal
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryRouteRead, routeWindow, routeTerminal,
      sameRoute, routePkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
