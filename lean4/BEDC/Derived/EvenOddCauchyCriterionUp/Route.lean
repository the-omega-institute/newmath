import BEDC.Derived.EvenOddCauchyCriterionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def EvenOddCauchyCriterionCarrier (A B SA SB eps M D F R H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory SA ∧ UnaryHistory SB ∧
    UnaryHistory eps ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory F ∧
      UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N

theorem EvenOddCauchyCriterionCarrier_real_seal_route
    {A B SA SB eps M D F R H C P N selected budgetRead toleranceRead fusionRead
      sealRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N →
      Cont eps SA selected →
        Cont selected M budgetRead →
          Cont budgetRead D toleranceRead →
            Cont toleranceRead F fusionRead →
              Cont fusionRead R sealRead →
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory SA ∧ UnaryHistory SB ∧
                  UnaryHistory eps ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory F ∧
                    UnaryHistory R ∧ UnaryHistory selected ∧ UnaryHistory budgetRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory fusionRead ∧
                        UnaryHistory sealRead ∧ Cont eps SA selected ∧
                          Cont selected M budgetRead ∧ Cont budgetRead D toleranceRead ∧
                            Cont toleranceRead F fusionRead ∧ Cont fusionRead R sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier selectedRoute budgetRoute toleranceRoute fusionRoute sealRoute
  obtain ⟨aUnary, bUnary, saUnary, sbUnary, epsUnary, mUnary, dUnary, fUnary,
    rUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed epsUnary saUnary selectedRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed selectedUnary mUnary budgetRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed budgetUnary dUnary toleranceRoute
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed toleranceUnary fUnary fusionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed fusionUnary rUnary sealRoute
  exact
    ⟨aUnary, bUnary, saUnary, sbUnary, epsUnary, mUnary, dUnary, fUnary, rUnary,
      selectedUnary, budgetUnary, toleranceUnary, fusionUnary, sealUnary, selectedRoute,
      budgetRoute, toleranceRoute, fusionRoute, sealRoute⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
