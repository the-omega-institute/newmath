import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyPrincipalFilterUp : Type where
  | mk (A G F U B H K P N : BHist) : CauchyPrincipalFilterUp
  deriving DecidableEq

end BEDC.Derived
