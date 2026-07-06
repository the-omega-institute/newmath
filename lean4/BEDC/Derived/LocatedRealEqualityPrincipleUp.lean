import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedRealEqualityPrincipleUp : Type where
  | mk (X Y L R W D A H C P N : BHist) : LocatedRealEqualityPrincipleUp
  deriving DecidableEq

end BEDC.Derived
