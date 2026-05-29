import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MarkedRealUp : Type where
  | mk (R S A L Z Pm Nm Q H C K N : BHist) : MarkedRealUp
  deriving DecidableEq

end BEDC.Derived
