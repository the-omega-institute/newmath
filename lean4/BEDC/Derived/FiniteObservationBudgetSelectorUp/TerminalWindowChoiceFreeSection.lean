import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_window_choice_free_section
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal sectionRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H sectionRow ->
          PkgSig bundle sectionRow pkg ->
            UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
              UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory terminal ∧
                UnaryHistory sectionRow ∧ Cont B S W ∧ Cont W D R ∧
                  Cont R E terminal ∧ Cont terminal H sectionRow ∧ hsame C terminal ∧
                    hsame N E ∧ PkgSig bundle sectionRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute sectionRoute sectionPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, routeW, routeR, routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unarySection : UnaryHistory sectionRow :=
    unary_cont_closed unaryTerminal unaryH sectionRoute
  have sameTerminal : hsame C terminal :=
    cont_deterministic routeC terminalRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryTerminal,
      unarySection, routeW, routeR, terminalRoute, sectionRoute, sameTerminal,
      sameName, sectionPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
