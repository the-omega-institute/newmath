import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BrentSalaminPiUp : Type where
  | mk (A R D S Q H C P N : BHist) : BrentSalaminPiUp

end BEDC.Derived
