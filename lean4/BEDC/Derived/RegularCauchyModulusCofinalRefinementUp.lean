import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyModulusCofinalRefinementUp : Type where
  | mk
      (sourceRow refinementRow windowRow readbackRow toleranceRow sealRow transportRow replayRow
        provenanceRow nameRow : BHist) :
      RegularCauchyModulusCofinalRefinementUp
  deriving DecidableEq

end BEDC.Derived
