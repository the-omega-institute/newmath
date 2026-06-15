import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FuchsianGroupActionUp : Type where
  | mk (D W M B H C P N : BHist) : FuchsianGroupActionUp
  deriving DecidableEq

end BEDC.Derived
