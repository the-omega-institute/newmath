import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IshiharaFiniteTestBoundaryUp : Type where
  | mk
      (branchWindow positiveTest negativeTest realSeal completionRefusal : BHist) :
      IshiharaFiniteTestBoundaryUp
  deriving DecidableEq

end BEDC.Derived
