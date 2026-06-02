import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyDensityUp : Type where
  | mk (Q S R A E H C P N : BHist) : RegularCauchyDensityUp
  deriving DecidableEq

namespace RegularCauchyDensityUp

def fields : RegularCauchyDensityUp → List BHist
  | RegularCauchyDensityUp.mk Q S R A E H C P N => [Q, S, R, A, E, H, C, P, N]

theorem field_count (x : RegularCauchyDensityUp) : (fields x).length = 9 := by
  cases x
  rfl

end RegularCauchyDensityUp
end BEDC.Derived
