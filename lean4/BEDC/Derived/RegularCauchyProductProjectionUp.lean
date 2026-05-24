import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyProductProjectionUp : Type where
  | mk
      (productPacket leftReadback rightReadback productModulus windows dyadicTolerance
        leftHandoff rightHandoff realSeal transport replay provenance name : BHist) :
      RegularCauchyProductProjectionUp
  deriving DecidableEq

end BEDC.Derived
