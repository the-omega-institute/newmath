import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FiniteObservationBudgetSelectorCarrier_cofinal_route_choice_freeness
    [AskSetup] (_ps : PackageSetup)
    {B S W D R E H C P N terminal terminal' cofinal cofinal' : BHist} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E terminal →
        Cont terminal H cofinal →
          Cont R E terminal' →
            Cont terminal' H cofinal' →
              hsame terminal terminal' ∧ hsame cofinal cofinal' := by
  -- BEDC touchpoint anchor: BHist Cont hsame PackageSetup
  intro _carrier terminalRoute cofinalRoute terminalRoute' cofinalRoute'
  have terminalSame : hsame terminal terminal' :=
    cont_respects_hsame (hsame_refl R) (hsame_refl E) terminalRoute terminalRoute'
  have cofinalSame : hsame cofinal cofinal' :=
    cont_respects_hsame terminalSame (hsame_refl H) cofinalRoute cofinalRoute'
  exact ⟨terminalSame, cofinalSame⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
