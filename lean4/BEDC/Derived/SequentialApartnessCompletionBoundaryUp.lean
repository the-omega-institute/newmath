import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SequentialApartnessCompletionBoundaryUp : Type where
  | mk (A Q L S R D E H C P N : BHist) : SequentialApartnessCompletionBoundaryUp
  deriving DecidableEq

end BEDC.Derived
