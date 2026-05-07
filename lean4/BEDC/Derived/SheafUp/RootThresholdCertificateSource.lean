import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SheafRootThresholdCertificateSource
    (point openHist sectionHist germ restrictedOpen restrictedGerm ambient member overlap
      route : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    hsame openHist restrictedOpen ∧
      Cont restrictedOpen sectionHist restrictedGerm ∧
        SheafBHistCoverNerveLedger ambient member overlap route germ

theorem SheafRootThresholdCertificateSource_readback
    {point openHist sectionHist germ restrictedOpen restrictedGerm ambient member overlap
      route : BHist} :
    SheafRootThresholdCertificateSource point openHist sectionHist germ restrictedOpen
        restrictedGerm ambient member overlap route ->
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm ∧
          SheafBHistCoverNerveLedger ambient member overlap route germ := by
  intro source
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback source.left source.right.left
      source.right.right.left
  exact And.intro readback.left (And.intro readback.right source.right.right.right)

end BEDC.Derived.SheafUp
