import BEDC.Derived.EvenOddCauchyCriterionUp.Route

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem EvenOddCauchyCriterionCarrier_parity_tail_fusion
    {A B SA SB eps M D F R H C P N evenRead oddRead budgetRead toleranceRead
      fusionRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N ->
      Cont eps SA evenRead ->
        Cont eps SB oddRead ->
          Cont evenRead M budgetRead ->
            Cont budgetRead D toleranceRead ->
              Cont toleranceRead F fusionRead ->
                UnaryHistory evenRead ∧ UnaryHistory oddRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory fusionRead ∧
                    hsame toleranceRead (append budgetRead D) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier evenRoute oddRoute budgetRoute toleranceRoute fusionRoute
  obtain ⟨_aUnary, _bUnary, saUnary, sbUnary, epsUnary, mUnary, dUnary, fUnary,
    _rUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have evenUnary : UnaryHistory evenRead :=
    unary_cont_closed epsUnary saUnary evenRoute
  have oddUnary : UnaryHistory oddRead :=
    unary_cont_closed epsUnary sbUnary oddRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed evenUnary mUnary budgetRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed budgetUnary dUnary toleranceRoute
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed toleranceUnary fUnary fusionRoute
  have toleranceEndpoint : hsame toleranceRead (append budgetRead D) := toleranceRoute
  exact
    ⟨evenUnary, oddUnary, budgetUnary, toleranceUnary, fusionUnary, toleranceEndpoint⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
