import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure PointedSetUp : Type where
  carrier : BHist
  basePoint : BHist
  optionRoute : BHist
  productRoute : BHist
  wedgeRoute : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
