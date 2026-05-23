import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive DyadicLocatedCutUp : Type where
  | mk (L U G W R E H C P N : BEDC.FKernel.Hist.BHist) : DyadicLocatedCutUp
  deriving DecidableEq

end BEDC.Derived
