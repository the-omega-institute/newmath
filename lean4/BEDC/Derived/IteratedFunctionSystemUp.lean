import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IteratedFunctionSystemUp : Type where
  | mk
      (X M K F L R Q S A H C P N : BHist) :
      IteratedFunctionSystemUp

end BEDC.Derived
