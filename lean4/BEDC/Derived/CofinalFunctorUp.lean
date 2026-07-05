import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CofinalFunctorUp : Type where
  | mk (C D F L U W K H R P N : BHist) : CofinalFunctorUp

end BEDC.Derived
