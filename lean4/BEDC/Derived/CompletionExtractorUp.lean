import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompletionExtractorUp : Type where
  | mk : (g m s d q e H C P N : BHist) -> CompletionExtractorUp
  deriving DecidableEq

end BEDC.Derived
