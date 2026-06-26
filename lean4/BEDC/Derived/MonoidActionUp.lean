import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MonoidActionUp : Type where
  | mk (M X alpha I C H R P N : BHist) : MonoidActionUp
  deriving DecidableEq

end BEDC.Derived
