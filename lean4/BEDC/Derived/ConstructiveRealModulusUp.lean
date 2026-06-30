import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConstructiveRealModulusUp : Type where
  | mk : (s d q r a h c p n : BHist) -> ConstructiveRealModulusUp
  deriving DecidableEq

end BEDC.Derived
