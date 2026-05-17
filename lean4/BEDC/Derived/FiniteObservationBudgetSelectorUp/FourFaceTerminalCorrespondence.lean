import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_four_face_terminal_correspondence
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal cofinal sectionRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E terminal →
        Cont terminal H cofinal →
          Cont terminal E sectionRow →
            PkgSig bundle cofinal pkg →
              PkgSig bundle sectionRow pkg →
                UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                  Cont B S W ∧ Cont W D R ∧ Cont R E terminal ∧
                    Cont terminal H cofinal ∧ Cont terminal E sectionRow ∧ hsame N E ∧
                      PkgSig bundle cofinal pkg ∧ PkgSig bundle sectionRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier terminalRoute cofinalRoute sectionRoute cofinalPkg sectionPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, routeW, routeR, terminalRoute, cofinalRoute,
      sectionRoute, sameName, cofinalPkg, sectionPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
