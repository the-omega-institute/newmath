import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedUpperLowerPairUp : Type where
  | mk : (d s r e h c p n : BHist) → LocatedUpperLowerPairUp
  deriving DecidableEq

end BEDC.Derived
