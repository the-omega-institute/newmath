import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedIntervalFanBarrierUp : Type where
  | mk
      (interval fan compact dyadic stream regular real transport replay provenance name : BHist) :
      LocatedIntervalFanBarrierUp
  deriving DecidableEq

end BEDC.Derived
