import BEDC.FKernel.Hist

namespace BEDC.Derived

structure EventualEqualityUp where
  leftWindow : BEDC.FKernel.Hist.BHist
  rightWindow : BEDC.FKernel.Hist.BHist
  tailCut : BEDC.FKernel.Hist.BHist
  agreementRow : BEDC.FKernel.Hist.BHist

end BEDC.Derived
