import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RegularCauchyTailSealUp : Type where
  | mk
      (dyadicLedger streamWindow regularReadback thresholdModulus realTailSeal
        transport replay provenance namecert : BEDC.FKernel.Hist.BHist)

end BEDC.Derived
