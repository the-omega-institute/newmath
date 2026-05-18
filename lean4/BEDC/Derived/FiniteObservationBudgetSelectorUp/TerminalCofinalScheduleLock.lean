import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_cofinal_schedule_lock
    [AskSetup] [PackageSetup]
    {B S S' W D R E H C P N terminal sharedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      FiniteObservationBudgetSelectorCarrier B S' W D R E H C P N ->
        Cont R E terminal ->
          Cont W D sharedRoute ->
            PkgSig bundle terminal pkg ->
              UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
                UnaryHistory E ∧ UnaryHistory terminal ∧ Cont W D sharedRoute ∧
                  Cont R E terminal ∧ hsame C terminal ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _carrierAlternate terminalRoute sharedRoutePath terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, routeC,
    _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have sameTerminal : hsame C terminal :=
    cont_deterministic routeC terminalRoute
  exact
    ⟨unaryB, unaryW, unaryD, unaryR, unaryE, unaryTerminal, sharedRoutePath,
      terminalRoute, sameTerminal, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
