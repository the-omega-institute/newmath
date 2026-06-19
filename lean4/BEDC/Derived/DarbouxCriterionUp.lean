import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DarbouxCriterionUp : Type where
  | mk (P L U G T R E H C Q N : BHist) : DarbouxCriterionUp
  deriving DecidableEq

end BEDC.Derived
