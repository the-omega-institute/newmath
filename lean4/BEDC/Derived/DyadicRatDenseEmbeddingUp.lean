import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicRatDenseEmbeddingUp : Type where
  | mk
      (dyadic streamName regSeqRat realSeal transport replay provenance localName : BHist) :
      DyadicRatDenseEmbeddingUp
  deriving DecidableEq

end BEDC.Derived
