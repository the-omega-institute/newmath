import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RealUniformCauchyFilterCompletionUp : Type where
  | mk
      (realUniform cauchyCompletion cauchyFilter streamWindow regSeqRat dyadicRealSeal
        transport replay provenance localName : BEDC.FKernel.Hist.BHist)

end BEDC.Derived
