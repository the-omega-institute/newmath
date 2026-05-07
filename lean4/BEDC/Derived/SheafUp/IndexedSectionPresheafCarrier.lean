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

theorem SheafIndexedSectionPresheafCarrier_endpoint_unary
    {point openHist sectionHist restriction identity composite germ : BHist} :
    SheafIndexedSectionPresheafCarrier point openHist sectionHist restriction identity
        composite germ ->
      UnaryHistory composite := by
  intro carrier
  exact (SheafIndexedSectionPresheafCarrier_carrier_rows carrier).right.right.left

theorem SheafCarrierSupport_obligation
    {point openHist sectionHist restriction identity composite germ : BHist} :
    SheafIndexedSectionPresheafCarrier point openHist sectionHist restriction identity
        composite germ ->
      SheafBHistPointGermLedger point openHist sectionHist germ ∧
        SheafRootFaceRead openHist germ SheafRootFaceLanding.restrictionRoute ∧
          UnaryHistory sectionHist ∧ UnaryHistory restriction ∧ UnaryHistory identity ∧
            UnaryHistory composite ∧ Cont sectionHist restriction identity ∧
              Cont restriction identity composite := by
  intro carrier
  have rows := SheafIndexedSectionPresheafCarrier_carrier_rows carrier
  exact And.intro rows.left
    (And.intro (SheafRootFaceRead.restrictionRoute rows.left.right.right)
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro rows.right.left
            (And.intro rows.right.right.left
              (And.intro rows.right.right.right.left rows.right.right.right.right))))))

def SheafIndexedSectionPresheafEndpointCarrier
    (openHist sectionHist restrictedHist : BHist) : Prop :=
  UnaryHistory openHist ∧ UnaryHistory sectionHist ∧ Cont openHist sectionHist restrictedHist

theorem SheafIndexedSectionPresheafEndpointCarrier_endpoint_unary
    {openHist sectionHist restrictedHist : BHist} :
    SheafIndexedSectionPresheafEndpointCarrier openHist sectionHist restrictedHist ->
      UnaryHistory restrictedHist := by
  intro carrier
  exact unary_cont_closed carrier.left carrier.right.left carrier.right.right

end BEDC.Derived.SheafUp
