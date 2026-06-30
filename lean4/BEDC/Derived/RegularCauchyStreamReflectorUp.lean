import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyStreamReflectorUp : Type where
  | mk
      (streamWindow dyadicTolerance regularReadback realSeal transport replay provenance localName :
        BHist) :
      RegularCauchyStreamReflectorUp
  deriving DecidableEq

end BEDC.Derived
