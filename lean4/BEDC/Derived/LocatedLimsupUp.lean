import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedLimsupUp : Type where
  | mk (S T W Q U R E H C P N : BHist) : LocatedLimsupUp
  deriving DecidableEq

end BEDC.Derived
