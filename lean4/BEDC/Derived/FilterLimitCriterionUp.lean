import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FilterLimitCriterionUp : Type where
  | mk
      (filterBase neighbourhood cauchy window readback realSeal transport replay criterion package name :
        BHist) :
      FilterLimitCriterionUp
  deriving DecidableEq

end BEDC.Derived
