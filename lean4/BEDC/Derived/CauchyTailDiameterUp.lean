import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyTailDiameterUp : Type where
  | mk
      (source threshold leftIndex rightIndex tolerance bound window transport replay provenance
        localName : BHist) :
      CauchyTailDiameterUp
  deriving DecidableEq

end BEDC.Derived
