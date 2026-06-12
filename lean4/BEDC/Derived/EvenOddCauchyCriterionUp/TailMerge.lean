import BEDC.Derived.EvenOddCauchyCriterionUp.CrossParityHandoffNonEscape
import BEDC.Derived.EvenOddCauchyCriterionUp.ParityTailFusion

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem EvenOddCauchyCriterionTailMerge
    {A B SA SB eps M D F R H C P N evenRead oddRead budgetRead toleranceRead
      fusionRead sealRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N ->
      Cont eps SA evenRead ->
        Cont eps SB oddRead ->
          Cont evenRead M budgetRead ->
            Cont budgetRead D toleranceRead ->
              Cont toleranceRead F fusionRead ->
                Cont fusionRead R sealRead ->
                  UnaryHistory evenRead ∧ UnaryHistory oddRead ∧
                    UnaryHistory toleranceRead ∧ hsame toleranceRead (append budgetRead D) ∧
                      UnaryHistory fusionRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: EvenOddCauchyCriterionCarrier BHist Cont hsame UnaryHistory
  intro carrier evenRoute oddRoute budgetRoute toleranceRoute fusionRoute sealRoute
  have fusionData :=
    EvenOddCauchyCriterionCarrier_parity_tail_fusion
      carrier evenRoute oddRoute budgetRoute toleranceRoute fusionRoute
  have sealData :=
    EvenOddCauchyCriterionCrossParityHandoffNonEscape
      carrier evenRoute oddRoute budgetRoute toleranceRoute fusionRoute sealRoute
  exact
    ⟨fusionData.left, fusionData.right.left, fusionData.right.right.right.left,
      fusionData.right.right.right.right.right, fusionData.right.right.right.right.left,
      sealData.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
