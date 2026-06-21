import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure LebesgueCoveringDimensionInductionUp : Type where
  topologySource : BHist
  coveringDimensionRow : BHist
  smallInductiveRow : BHist
  largeInductiveRow : BHist
  normalSpaceBoundary : BHist
  finiteCoverRefinement : BHist
  boundaryRecursion : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
