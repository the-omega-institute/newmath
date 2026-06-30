import BEDC.FKernel.Hist

namespace BEDC.Derived.LocallyConnectedContinuumUp

open BEDC.FKernel.Hist

inductive LocallyConnectedContinuumUp : Type where
  | mk (K C L W R H T P N : BHist) : LocallyConnectedContinuumUp

end BEDC.Derived.LocallyConnectedContinuumUp
