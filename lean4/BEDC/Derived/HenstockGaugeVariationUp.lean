import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HenstockGaugeVariationUp : Type where
  | mk
      (gaugeAdmission variationLedger regulatedReadback stieltjesTransfer realSeal
        transport replay provenance name : BHist) :
      HenstockGaugeVariationUp

end BEDC.Derived
