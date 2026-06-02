import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedSupremumModulusUp : Type where
  | mk (B I D R E H C P N : BHist) : LocatedSupremumModulusUp
  deriving DecidableEq

end BEDC.Derived
