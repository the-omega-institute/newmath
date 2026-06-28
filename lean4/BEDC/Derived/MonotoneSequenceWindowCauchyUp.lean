import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MonotoneSequenceWindowCauchyUp : Type where
  | mk (M B S R D E H C P N : BHist) : MonotoneSequenceWindowCauchyUp
  deriving DecidableEq

end BEDC.Derived
