import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FiniteObservationBudgetSelectorCarrier_terminal_section_pullback_uniqueness
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal0 terminal1 section0 section1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal0 ->
        Cont terminal0 E section0 ->
          Cont R E terminal1 ->
            Cont terminal1 E section1 ->
              PkgSig bundle section0 pkg ->
                PkgSig bundle section1 pkg ->
                  hsame terminal0 terminal1 ∧ hsame section0 section1 ∧
                    PkgSig bundle section0 pkg ∧ PkgSig bundle section1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier terminalRoute0 sectionRoute0 terminalRoute1 sectionRoute1 sectionPkg0
    sectionPkg1
  obtain ⟨_unaryB, _unaryS, _unaryD, _unaryE, _unaryH, _routeW, _routeR, _routeC,
    _sameName⟩ := carrier
  have sameTerminal : hsame terminal0 terminal1 :=
    cont_deterministic terminalRoute0 terminalRoute1
  have sameSection : hsame section0 section1 :=
    cont_respects_hsame sameTerminal (hsame_refl E) sectionRoute0 sectionRoute1
  exact ⟨sameTerminal, sameSection, sectionPkg0, sectionPkg1⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
