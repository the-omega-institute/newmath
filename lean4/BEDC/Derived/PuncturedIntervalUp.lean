import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PuncturedIntervalUp : Type where
  | mk (I X R D W Q S H C P N : BHist) : PuncturedIntervalUp

end BEDC.Derived
