import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HausdorffCompletionFunctorUp : Type where
  | mk (X Y M C U P H R Q N : BHist) : HausdorffCompletionFunctorUp
  deriving DecidableEq

end BEDC.Derived
