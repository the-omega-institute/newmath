import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchySequenceModulusChainUp : Type where
  | mk
      (streamWindow regSeqReadback dyadicTolerance modulusChain realSeal transport replay
        provenance name : BHist) :
      CauchySequenceModulusChainUp
  deriving DecidableEq

end BEDC.Derived
