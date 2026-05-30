import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetacicCandidateNormalizationConfluenceHandoffUp : Type where
  | mk (A K N F C D B H R P L : BHist) :
      MetacicCandidateNormalizationConfluenceHandoffUp
  deriving DecidableEq

end BEDC.Derived
