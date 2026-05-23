import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure CauchyContinuousMapUp where
  windows : BHist
  imageReadback : BHist
  toleranceLedger : BHist
  realSealHandoff : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist
deriving DecidableEq

end BEDC.Derived
