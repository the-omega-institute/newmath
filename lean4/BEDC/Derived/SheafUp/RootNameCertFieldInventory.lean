import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SheafRootNameCertFieldInventory (point openHist sectionHist germ : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    SemanticNameCert
      (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
      (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
      (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
      hsame

end BEDC.Derived.SheafUp
