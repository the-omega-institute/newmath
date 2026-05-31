import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive CompleteMetricProductUp : Type where
  | mk
      (M X Y SX SY RX RY AX AY LX LY Pi L H C P N : BEDC.FKernel.Hist.BHist) :
      CompleteMetricProductUp
  deriving DecidableEq

end BEDC.Derived
