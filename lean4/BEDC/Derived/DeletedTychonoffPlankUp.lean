import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure DeletedTychonoffPlankUp : Type where
  plankRow : BHist
  deletedCorner : BHist
  productBoundary : BHist
  topologyRow : BHist
  compactRow : BHist
  sierpinskiRow : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
