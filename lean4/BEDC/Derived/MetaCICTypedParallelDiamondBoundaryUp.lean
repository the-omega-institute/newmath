import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetaCICTypedParallelDiamondBoundaryUp : Type where
  | mk (W S K J R C N B O H T P M : BHist) : MetaCICTypedParallelDiamondBoundaryUp
  deriving DecidableEq

end BEDC.Derived
