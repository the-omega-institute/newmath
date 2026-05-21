import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompletionUniquenessUp : Type where
  | mk (D S R E H F L T C P N : BHist) : CompletionUniquenessUp
  deriving DecidableEq

end BEDC.Derived
