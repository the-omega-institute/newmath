import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure CauchyCompletionMonadMultiplicationUp where
  outer : BHist
  inner : BHist
  bind : BHist
  law : BHist
  windows : BHist
  readback : BHist
  tolerance : BHist
  sealRow : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameRow : BHist
  deriving Repr

end BEDC.Derived
