import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_cofinal_window_exhaustion
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal cofinal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H cofinal ->
          PkgSig bundle cofinal pkg ->
            UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
              UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory terminal ∧
                UnaryHistory cofinal ∧ Cont B S W ∧ Cont W D R ∧
                  Cont R E terminal ∧ Cont terminal H cofinal ∧ hsame N E ∧
                    PkgSig bundle cofinal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute cofinalRoute cofinalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryCofinal : UnaryHistory cofinal :=
    unary_cont_closed unaryTerminal unaryH cofinalRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryTerminal, unaryCofinal,
      routeW, routeR, terminalRoute, cofinalRoute, sameName, cofinalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
