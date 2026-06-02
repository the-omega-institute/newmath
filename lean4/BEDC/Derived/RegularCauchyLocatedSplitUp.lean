import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyLocatedSplitUp : Type where
  | mk :
      (source located budget window readback realSeal transport replay provenance localName : BHist) →
      RegularCauchyLocatedSplitUp
  deriving DecidableEq

end BEDC.Derived
