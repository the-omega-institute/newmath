import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopLocatedRealApartnessModulusUp : Type where
  | mk (L E R D B M H C P N : BHist) : BishopLocatedRealApartnessModulusUp

end BEDC.Derived
