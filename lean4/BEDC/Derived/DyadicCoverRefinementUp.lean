import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicCoverRefinementUp : Type where
  | mk
      (leftCover rightCover commonRefinement leftRestriction rightRestriction
        transport routes provenance name : BHist) :
      DyadicCoverRefinementUp
  deriving DecidableEq

end BEDC.Derived
