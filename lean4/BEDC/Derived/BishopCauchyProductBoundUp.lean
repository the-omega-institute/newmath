import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive BishopCauchyProductBoundUp : Type where
  | mk
      (sourceLeft sourceRight windowLeft windowRight boundLeft boundRight dyadicLedger
        cauchyProduct regularProduct realSeal transport replay provenance name :
          _root_.BEDC.FKernel.Hist.BHist) :
      BishopCauchyProductBoundUp

end BEDC.Derived
