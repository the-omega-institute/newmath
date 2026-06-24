import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HausdorffCompletionPullbackUp : Type where
  | mk (S W D P0 P1 H0 H1 U T C Q N : BHist) : HausdorffCompletionPullbackUp
  deriving DecidableEq

end BEDC.Derived
