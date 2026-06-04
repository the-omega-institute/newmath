import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyInterleavingStabilityUp : Type where
  | mk
      (leftSource rightSource leftSchedule rightSchedule selector sharedModulus
        selectedWindows realSeal transport replay provenance name : BHist) :
      RegularCauchyInterleavingStabilityUp
  deriving DecidableEq

end BEDC.Derived
