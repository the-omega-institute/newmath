import BEDC.FKernel.Hist

namespace BEDC.Derived.FiniteWindowRegSeqRatRefinementUp

open BEDC.FKernel.Hist

inductive FiniteWindowRegSeqRatRefinementUp : Type where
  | mk (S R D M W E H C P N : BHist) : FiniteWindowRegSeqRatRefinementUp
  deriving DecidableEq

end BEDC.Derived.FiniteWindowRegSeqRatRefinementUp
