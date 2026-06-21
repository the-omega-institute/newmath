import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure CollectionwiseNormalUp : Type where
  topologySource : BHist
  normalSpaceRow : BHist
  discreteClosedFamily : BHist
  locallyFiniteOpenRefinement : BHist
  paracompactHandoff : BHist
  urysohnHandoff : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
