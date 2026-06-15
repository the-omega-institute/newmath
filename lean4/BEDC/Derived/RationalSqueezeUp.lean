import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RationalSqueezeUp : Type where
  | mk
      (lower upper middle tolerance regSeqRat realSeal locatedOrder transport replay provenance
        name : BHist) :
      RationalSqueezeUp
  deriving DecidableEq

end BEDC.Derived
