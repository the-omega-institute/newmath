import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformFilterBaseUp : Type where
  | mk (U B C S R D A H K P N : BHist) : UniformFilterBaseUp

end BEDC.Derived
