import BEDC.Derived.EvenOddCauchyCriterionUp.Route

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem EvenOddCauchyCriterionCrossParityHandoffNonEscape
    {A B SA SB eps M D F R H C P N evenRead oddRead budgetRead toleranceRead fusionRead
      sealRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N ->
      Cont eps SA evenRead ->
        Cont eps SB oddRead ->
          Cont evenRead M budgetRead ->
            Cont budgetRead D toleranceRead ->
              Cont toleranceRead F fusionRead ->
                Cont fusionRead R sealRead ->
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory SA ∧ UnaryHistory SB ∧
                    UnaryHistory eps ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory F ∧
                      UnaryHistory R ∧ UnaryHistory evenRead ∧ UnaryHistory oddRead ∧
                        UnaryHistory budgetRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory fusionRead ∧ UnaryHistory sealRead ∧
                            Cont toleranceRead F fusionRead ∧ Cont fusionRead R sealRead := by
  -- BEDC touchpoint anchor: EvenOddCauchyCriterionCarrier BHist Cont UnaryHistory
  intro carrier evenRoute oddRoute budgetRoute toleranceRoute fusionRoute sealRoute
  obtain ⟨aUnary, bUnary, saUnary, sbUnary, epsUnary, mUnary, dUnary, fUnary,
    rUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
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
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed fusionUnary rUnary sealRoute
  exact
    ⟨aUnary, bUnary, saUnary, sbUnary, epsUnary, mUnary, dUnary, fUnary, rUnary,
      evenUnary, oddUnary, budgetUnary, toleranceUnary, fusionUnary, sealUnary, fusionRoute,
      sealRoute⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
