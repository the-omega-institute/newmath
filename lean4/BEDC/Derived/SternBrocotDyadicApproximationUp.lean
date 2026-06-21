import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SternBrocotDyadicApproximationUp : Type where
  | mk (S B D Q W R E H C P N : BHist) : SternBrocotDyadicApproximationUp

end BEDC.Derived
