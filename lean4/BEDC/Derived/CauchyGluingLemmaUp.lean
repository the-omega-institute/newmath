import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyGluingLemmaUp : Type where
  | mk (S0 S1 W0 W1 D R E H C P N : BHist) : CauchyGluingLemmaUp
  deriving DecidableEq

end BEDC.Derived
