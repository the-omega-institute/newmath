import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyCompletionUnitCounitUp : Type where
  | mk
      (dyadicRatCore streamName regSeqRat realSeal unit counit triangle transport replay
        provenance localName : BHist) :
      RegularCauchyCompletionUnitCounitUp
  deriving DecidableEq

end BEDC.Derived
