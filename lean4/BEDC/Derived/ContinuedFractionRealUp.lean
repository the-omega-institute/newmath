import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ContinuedFractionRealUp : Type where
  | mk (A C D W R E H K P N : BHist) : ContinuedFractionRealUp

end BEDC.Derived
