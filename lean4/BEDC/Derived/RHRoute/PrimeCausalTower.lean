import BEDC.Derived.RHRoute.ConstructiveRHStatement

namespace BEDC.Derived.RHRoute.PrimeCausalTower

open BEDC.Derived.RHRoute.ConstructiveRHStatement

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

structure EntireCarrier where
  E : RatComplex -> RatComplex
  Esharp : RatComplex -> RatComplex
  A_E : RatComplex -> RatComplex

structure PrimeEvent where
  code : Nat

structure PrimeTransfer where
  act : EntireCarrier -> EntireCarrier

structure AssociatedAEqualsXi (E : EntireCarrier) where
  Xi : RatComplex -> RatComplex
  A_E_reads_Xi :
    forall z : RatComplex, RatComplexEq (E.A_E z) (Xi z)

structure PrimeCausalTower where
  HB : EntireCarrier -> Prop
  E0 : EntireCarrier
  E0_HB : HB E0
  primeObs : Nat -> PrimeEvent
  transfer : PrimeEvent -> PrimeTransfer
  transfer_preserves_HB :
    forall p : PrimeEvent, forall E : EntireCarrier,
      HB E -> HB ((transfer p).act E)

def eTower (T : PrimeCausalTower) : Nat -> EntireCarrier
  | 0 => T.E0
  | Nat.succ n => (T.transfer (T.primeObs n)).act (eTower T n)

theorem eTower_HB (T : PrimeCausalTower) :
    forall n : Nat, T.HB (eTower T n) := by
  intro n
  induction n with
  | zero =>
      exact T.E0_HB
  | succ n ih =>
      exact T.transfer_preserves_HB (T.primeObs n) (eTower T n) ih

-- These four tags isolate the forward-from-primes frontier.  At least one
-- carries RH-level difficulty.  They are not discharged by this module, and
-- the tower does not consume zero-location input, Weil-Li positivity, an
-- `E_xi in HB` premise, or innerness of a terminal theta ratio.
-- No backward-from-answer: the forward-from-primes transfer obligations must
-- be proved without assuming the terminal Xi/HB conclusion.
inductive PrimeTowerFrontierObligation where
  | primeTransfer_is_JContractive
  | primeTransfer_matches_Euler_event
  | limit_HB
  | terminal_associatedA_eq_Xi

def canonicalPrimeTowerFrontierObligations :
    List PrimeTowerFrontierObligation :=
  [ PrimeTowerFrontierObligation.primeTransfer_is_JContractive,
    PrimeTowerFrontierObligation.primeTransfer_matches_Euler_event,
    PrimeTowerFrontierObligation.limit_HB,
    PrimeTowerFrontierObligation.terminal_associatedA_eq_Xi ]

structure TowerLimit (T : PrimeCausalTower) where
  Einf : EntireCarrier
  limit_HB : T.HB Einf
  terminal_associatedA_eq_Xi : AssociatedAEqualsXi Einf
  deBranges_HB_terminal_to_ConstructiveRH :
    T.HB Einf -> AssociatedAEqualsXi Einf -> ConstructiveRH

theorem RH_from_generated_BEDC_zeta
    (T : PrimeCausalTower) (L : TowerLimit T) :
    ConstructiveRH := by
  exact
    L.deBranges_HB_terminal_to_ConstructiveRH
      L.limit_HB
      L.terminal_associatedA_eq_Xi

theorem primeTowerFrontierObligation_count :
    canonicalPrimeTowerFrontierObligations.length = 4 := by
  rfl

end BEDC.Derived.RHRoute.PrimeCausalTower
