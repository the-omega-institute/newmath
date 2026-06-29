import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RapidCauchySubsequenceUp : Type where
  | mk
      (sourceSequence rapidRate monotoneIndex streamWindow dyadicTolerance regSeqReadback
        realSeal diagonalHandoff rateHandoff transport replay provenance localNameCert : BHist) :
      RapidCauchySubsequenceUp
  deriving DecidableEq

end BEDC.Derived
