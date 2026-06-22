import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BackwardDifferentiationFormulaUp : Type where
  | mk (O W C D R S H K P N : BHist) : BackwardDifferentiationFormulaUp

end BEDC.Derived
