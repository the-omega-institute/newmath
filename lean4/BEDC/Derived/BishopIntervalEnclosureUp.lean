import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopIntervalEnclosureUp : Type where
  | mk (L U Q D R S H C P N : BHist) : BishopIntervalEnclosureUp
  deriving DecidableEq

end BEDC.Derived
