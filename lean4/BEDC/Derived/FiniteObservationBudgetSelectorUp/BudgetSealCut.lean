import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_budget_seal_cut
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N lower upper terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont B S lower →
        Cont W D upper →
          Cont R E terminal →
            PkgSig bundle terminal pkg →
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory terminal ∧
                Cont B S lower ∧ Cont W D upper ∧ Cont R E terminal ∧
                  hsame lower W ∧ hsame upper R ∧ hsame N E ∧
                    PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier lowerRoute upperRoute terminalRoute terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, windowRoute,
    _sealRoute, sameName⟩ := carrier
  have lowerUnary : UnaryHistory lower :=
    unary_cont_closed unaryB unaryS lowerRoute
  have carrierWindowUnary : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have upperUnary : UnaryHistory upper :=
    unary_cont_closed carrierWindowUnary unaryD upperRoute
  have carrierRegularUnary : UnaryHistory R :=
    unary_cont_closed carrierWindowUnary unaryD windowRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed carrierRegularUnary unaryE terminalRoute
  have sameLower : hsame lower W :=
    cont_respects_hsame (hsame_refl B) (hsame_refl S) lowerRoute budgetRoute
  have sameUpper : hsame upper R :=
    cont_respects_hsame (hsame_refl W) (hsame_refl D) upperRoute windowRoute
  exact
    ⟨lowerUnary, upperUnary, terminalUnary, lowerRoute, upperRoute, terminalRoute,
      sameLower, sameUpper, sameName, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
