import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetricCompletionSequenceUp : Type where
  | mk (X S M W L U H C P N : BHist) : MetricCompletionSequenceUp
  deriving DecidableEq

end BEDC.Derived
