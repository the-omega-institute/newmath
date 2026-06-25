import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive KnoppTailCondensationUp : Type where
  | mk (S T B D R A H C P N : BHist) : KnoppTailCondensationUp
  deriving DecidableEq

end BEDC.Derived
