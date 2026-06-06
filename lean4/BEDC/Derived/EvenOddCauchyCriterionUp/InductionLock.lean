import BEDC.Derived.EvenOddCauchyCriterionUp.Route

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem EvenOddCauchyInductionLock
    {A B SA SB eps M D F R H C P N selectedRead budgetRead toleranceRead
      fusionRead sealRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N ->
      Cont eps SA selectedRead ->
        Cont selectedRead M budgetRead ->
          Cont budgetRead D toleranceRead ->
            Cont toleranceRead F fusionRead ->
              Cont fusionRead R sealRead ->
                UnaryHistory selectedRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory fusionRead ∧
                    UnaryHistory sealRead ∧ hsame toleranceRead (append budgetRead D) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier selectedRoute budgetRoute toleranceRoute fusionRoute sealRoute
  obtain ⟨_aUnary, _bUnary, saUnary, _sbUnary, epsUnary, mUnary, dUnary, fUnary,
    rUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed epsUnary saUnary selectedRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed selectedUnary mUnary budgetRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed budgetUnary dUnary toleranceRoute
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed toleranceUnary fUnary fusionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed fusionUnary rUnary sealRoute
  have toleranceEndpoint : hsame toleranceRead (append budgetRead D) := toleranceRoute
  exact
    ⟨selectedUnary, budgetUnary, toleranceUnary, fusionUnary, sealUnary, toleranceEndpoint⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
