import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealSequentialApartnessUp : Type where
  | mk (L R W Q D A J E H C P N : BHist) : RealSequentialApartnessUp
  deriving DecidableEq

end BEDC.Derived
