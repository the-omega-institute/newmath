import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TriggerHypergraphReliabilityUp : Type where
  | mk (B E R L W D A H C P N : BHist) : TriggerHypergraphReliabilityUp
  deriving DecidableEq

end BEDC.Derived
