import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedClosedSetDistanceUp : Type where
  | mk (M S Q L D R W H C P N : BHist) : LocatedClosedSetDistanceUp

end BEDC.Derived
