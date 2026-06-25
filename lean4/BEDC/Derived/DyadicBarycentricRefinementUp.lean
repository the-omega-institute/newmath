import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicBarycentricRefinementUp : Type where
  | mk (D I M K S R Q H C P N : BHist) : DyadicBarycentricRefinementUp

end BEDC.Derived
