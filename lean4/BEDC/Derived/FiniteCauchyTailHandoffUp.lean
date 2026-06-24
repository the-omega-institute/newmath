import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteCauchyTailHandoffUp : Type where
  | mk
      (regSeqRat streamName dyadicRatCore cauchyModulus tailSelector realSeal transport
        continuation provenance localNameCert : BHist) :
      FiniteCauchyTailHandoffUp
  deriving DecidableEq

end BEDC.Derived
