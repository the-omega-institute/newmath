import BEDC.Derived.SheafUp.IndexedSectionPresheafCarrier

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafCarrierSupport_obligation_rows
    {point openHist sectionHist restriction identity composite germ ambient member overlap route
      coverGerm : BHist} :
    SheafIndexedSectionPresheafCarrier point openHist sectionHist restriction identity
        composite germ ->
      SheafBHistCoverNerveLedger ambient member overlap route coverGerm ->
        SheafBHistPointGermLedger point openHist sectionHist germ ∧ UnaryHistory identity ∧
          UnaryHistory composite ∧
            SheafBHistCoverNerveLedger ambient member overlap route coverGerm ∧
              UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧
                Cont overlap route coverGerm := by
  intro carrier cover
  have carrierRows :
      SheafBHistPointGermLedger point openHist sectionHist germ ∧ UnaryHistory identity ∧
        UnaryHistory composite ∧ Cont sectionHist restriction identity ∧
          Cont restriction identity composite :=
    SheafIndexedSectionPresheafCarrier_carrier_rows carrier
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro carrierRows.right.right.left
        (And.intro cover
          (And.intro cover.left
            (And.intro cover.right.left
              (And.intro cover.right.right.left cover.right.right.right.right))))))

end BEDC.Derived.SheafUp
