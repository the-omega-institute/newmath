import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CartanAngularBoundaryInvariantUp : Type where
  | mk : (b q m s phi o h c p n : BHist) -> CartanAngularBoundaryInvariantUp
  deriving DecidableEq

end BEDC.Derived
