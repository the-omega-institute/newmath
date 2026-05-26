import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchySequenceTailFilterCompletionUp : Type where
  | mk (T F C D W R E H K P N : BHist) : CauchySequenceTailFilterCompletionUp
  deriving DecidableEq

end BEDC.Derived
