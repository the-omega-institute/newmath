import BEDC.Derived.SheafUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafIndexedSectionPresheafCarrier
    (point openHist sectionHist restriction identity composite germ : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧ UnaryHistory sectionHist ∧
    UnaryHistory restriction ∧ Cont sectionHist restriction identity ∧
      Cont restriction identity composite

theorem SheafIndexedSectionPresheafCarrier_carrier_rows
    {point openHist sectionHist restriction identity composite germ : BHist} :
    SheafIndexedSectionPresheafCarrier point openHist sectionHist restriction identity
        composite germ ->
      SheafBHistPointGermLedger point openHist sectionHist germ ∧ UnaryHistory identity ∧
        UnaryHistory composite ∧ Cont sectionHist restriction identity ∧
          Cont restriction identity composite := by
  intro carrier
  have identityUnary : UnaryHistory identity :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.left
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed carrier.right.right.left identityUnary carrier.right.right.right.right
  exact And.intro carrier.left
    (And.intro identityUnary
      (And.intro compositeUnary
        (And.intro carrier.right.right.right.left carrier.right.right.right.right)))

end BEDC.Derived.SheafUp
