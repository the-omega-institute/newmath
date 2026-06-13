import BEDC.Derived.EvenOddCauchyCriterionUp.Route

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem EvenOddCauchySingleModulus
    {A B SA SB eps M D F R H C P N selectedBudget ledgerRead fusionRead realRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N →
      Cont eps M selectedBudget →
        Cont selectedBudget D ledgerRead →
          Cont ledgerRead F fusionRead →
            Cont fusionRead R realRead →
              UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory F ∧ UnaryHistory R ∧
                UnaryHistory selectedBudget ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory fusionRead ∧ UnaryHistory realRead ∧
                    hsame ledgerRead (append selectedBudget D) := by
  -- BEDC touchpoint anchor: EvenOddCauchyCriterionCarrier BHist Cont hsame UnaryHistory
  intro carrier selectedRoute ledgerRoute fusionRoute realRoute
  obtain ⟨_aUnary, _bUnary, _saUnary, _sbUnary, epsUnary, mUnary, dUnary, fUnary,
    rUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectedUnary : UnaryHistory selectedBudget :=
    unary_cont_closed epsUnary mUnary selectedRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed selectedUnary dUnary ledgerRoute
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed ledgerUnary fUnary fusionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed fusionUnary rUnary realRoute
  have ledgerEndpoint : hsame ledgerRead (append selectedBudget D) := ledgerRoute
  exact
    ⟨mUnary, dUnary, fUnary, rUnary, selectedUnary, ledgerUnary, fusionUnary, realUnary,
      ledgerEndpoint⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
