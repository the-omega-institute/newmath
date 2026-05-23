import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RiemannRearrangementUp : Type where
  | mk (S Q P M Pi B G E H C K N : BHist) : RiemannRearrangementUp
  deriving DecidableEq

def riemannRearrangementFields : RiemannRearrangementUp -> List BHist
  | RiemannRearrangementUp.mk S Q P M Pi B G E H C K N =>
      [S, Q, P, M, Pi, B, G, E, H, C, K, N]

theorem riemannRearrangementFields_injective {x y : RiemannRearrangementUp} :
    riemannRearrangementFields x = riemannRearrangementFields y -> x = y := by
  intro h
  cases x with
  | mk S1 Q1 P1 M1 Pi1 B1 G1 E1 H1 C1 K1 N1 =>
      cases y with
      | mk S2 Q2 P2 M2 Pi2 B2 G2 E2 H2 C2 K2 N2 =>
          cases h
          rfl

end BEDC.Derived
