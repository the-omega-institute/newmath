import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive VanDerWaerdenProgressionUp : Type where
  | mk (N C K P A H R Q S : BHist) : VanDerWaerdenProgressionUp
  deriving DecidableEq

end BEDC.Derived
