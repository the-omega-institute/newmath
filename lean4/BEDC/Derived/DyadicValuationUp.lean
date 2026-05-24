import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicValuationUp : Type where
  | mk (M E Z V C T H R P N : BHist) : DyadicValuationUp
  deriving DecidableEq

def dyadicValuationFields : DyadicValuationUp -> List BHist
  | DyadicValuationUp.mk M E Z V C T H R P N => [M, E, Z, V, C, T, H, R, P, N]

theorem dyadicValuationFields_injective {x y : DyadicValuationUp} :
    dyadicValuationFields x = dyadicValuationFields y -> x = y := by
  intro h
  cases x with
  | mk M1 E1 Z1 V1 C1 T1 H1 R1 P1 N1 =>
      cases y with
      | mk M2 E2 Z2 V2 C2 T2 H2 R2 P2 N2 =>
          cases h
          rfl

end BEDC.Derived
