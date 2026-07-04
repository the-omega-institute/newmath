import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RiemannSeriesTheoremUp : Type where
  | mk (S Ppos Pneg W A T D E H C Q N : BHist) : RiemannSeriesTheoremUp
  deriving DecidableEq

end BEDC.Derived
