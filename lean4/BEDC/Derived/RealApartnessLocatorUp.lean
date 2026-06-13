import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealApartnessLocatorUp : Type where
  | mk (L A D S R O G E H C P N : BHist) : RealApartnessLocatorUp
  deriving DecidableEq

end BEDC.Derived
