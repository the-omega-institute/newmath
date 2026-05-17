import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_budget_prefix_pullback_inversion
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N prefixRow terminal sectionRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont B S prefixRow ->
        Cont R E terminal ->
          Cont terminal E sectionRow ->
            PkgSig bundle sectionRow pkg ->
              UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
                UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory prefixRow ∧
                  UnaryHistory terminal ∧ UnaryHistory sectionRow ∧
                    Cont B S prefixRow ∧ Cont B S W ∧ Cont W D R ∧
                      Cont R E terminal ∧ Cont terminal E sectionRow ∧ hsame prefixRow W ∧
                        hsame N E ∧ PkgSig bundle sectionRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier prefixRoute terminalRoute sectionRoute sectionPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    _carrierTerminalRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have prefixUnary : UnaryHistory prefixRow :=
    unary_cont_closed unaryB unaryS prefixRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have sectionUnary : UnaryHistory sectionRow :=
    unary_cont_closed terminalUnary unaryE sectionRoute
  have samePrefix : hsame prefixRow W :=
    cont_respects_hsame (hsame_refl B) (hsame_refl S) prefixRoute budgetRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, prefixUnary, terminalUnary,
      sectionUnary, prefixRoute, budgetRoute, regularRoute, terminalRoute, sectionRoute,
      samePrefix, sameName, sectionPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
