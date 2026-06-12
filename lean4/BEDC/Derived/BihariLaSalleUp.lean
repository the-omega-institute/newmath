import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BihariLaSalleUp : Type where
  | mk (I U W O G R Z H C P N : BHist) : BihariLaSalleUp

end BEDC.Derived
