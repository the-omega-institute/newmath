import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HopfFibrationUp : Type where
  | mk (S3 S2 F Pi C L V T R P N : BHist) : HopfFibrationUp
  deriving DecidableEq

end BEDC.Derived
