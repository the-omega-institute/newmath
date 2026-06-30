import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.RHRoute.PrimeCausalTower
import BEDC.Real.RatNumLogEnclosure
import BEDC.Derived.PrimeUp.DividesClosure

set_option maxHeartbeats 1000000

namespace BEDC.Derived.RHRoute.HalfPlaneEulerProduct

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.PrimeCausalTower
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

structure HP1WitnessRat (s : RatComplex) where
  alpha : Rat
  h_alpha_gt_one : ratLt ratOne alpha
  h_re_ge_alpha : ratLe alpha s.re

theorem ratLt_le_trans_local {x y z : Rat} :
    ratLt x y -> ratLe y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) yz
  · intro zx
    exact ratLt_not_ratLe_reverse xy (ratLe_trans yz zx)

theorem hp1_alpha_pos {s : RatComplex} (h : HP1WitnessRat s) :
    ratLt ratZero h.alpha :=
  ratLe_lt_trans ratOne_nonneg h.h_alpha_gt_one

theorem hp1_re_gt_one {s : RatComplex} (h : HP1WitnessRat s) :
    ratLt ratOne s.re :=
  ratLt_le_trans_local h.h_alpha_gt_one h.h_re_ge_alpha

theorem prime_nat_gt_one {p : Nat} (hp : IsPrime p) : 1 < p := by
  unfold IsPrime at hp
  have strict :
      NatUnaryStrictPrefix (BHist.e1 BHist.Empty)
        (natToUnary p) := hp.right.left
  have lengthLt :
      bwordLength (BHist.e1 BHist.Empty) <
        bwordLength (natToUnary p) :=
    NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
  change 1 < bwordLength (natToUnary p) at lengthLt
  rw [natToUnary_length] at lengthLt
  exact lengthLt

theorem prime_nat_pos {p : Nat} (hp : IsPrime p) : 0 < p :=
  Nat.lt_trans Nat.zero_lt_one (prime_nat_gt_one hp)

def primeUnitRadius (p : Nat) (hp : IsPrime p) : Rat :=
  ratDivApart ratOne (ratNat p)
    (ratApart0_of_pos (ratNat_pos_of_pos (prime_nat_pos hp)))

theorem primeUnitRadius_pos {p : Nat} (hp : IsPrime p) :
    ratLt ratZero (primeUnitRadius p hp) := by
  unfold primeUnitRadius
  exact div_pos ratOne_pos (ratNat_pos_of_pos (prime_nat_pos hp))

theorem primeUnitRadius_lt_one {p : Nat} (hp : IsPrime p) :
    ratLt (primeUnitRadius p hp) ratOne := by
  let den := ratNat p
  let denApart : ratApart0 den :=
    ratApart0_of_pos (ratNat_pos_of_pos (prime_nat_pos hp))
  let q := ratDivApart ratOne den denApart
  have denPos : ratLt ratZero den :=
    ratNat_pos_of_pos (prime_nat_pos hp)
  have qPos : ratLt ratZero q := by
    unfold q den denApart
    exact div_pos ratOne_pos (ratNat_pos_of_pos (prime_nat_pos hp))
  have oneLtDen : ratLt ratOne den := by
    unfold den
    exact ratNat_lt_of_nat_lt (prime_nat_gt_one hp)
  have scaled : ratLt (ratMul q ratOne) (ratMul q den) :=
    ratMul_lt_mul_left oneLtDen qPos
  have leftEq : RatEq (ratMul q ratOne) q :=
    ratMul_one_right q
  have rightEq : RatEq (ratMul q den) ratOne := by
    unfold q
    exact ratDivApart_mul_cancel_right denApart
  exact ratLt_of_RatEq_right
    (ratLt_of_RatEq_left (RatEq_symm leftEq) scaled)
    rightEq

structure QPrimeSymbol (p : Nat) (s : RatComplex) where
  prime : Nat
  point : RatComplex
  prime_eq : prime = p
  point_eq : point = s

structure LocatedComplexMagnitudeEnvelope where
  prime : Nat
  point : RatComplex
  absUB : Rat
  abs_nonneg : ratLe ratZero absUB

def qPrime (p : Nat) (s : RatComplex) : QPrimeSymbol p s :=
  { prime := p
    point := s
    prime_eq := rfl
    point_eq := rfl }

def qPrimeEnvelope (p : Nat) (hp : IsPrime p)
    (s : RatComplex) (_h : HP1WitnessRat s) :
    LocatedComplexMagnitudeEnvelope :=
  { prime := (qPrime p s).prime
    point := (qPrime p s).point
    absUB := primeUnitRadius p hp
    abs_nonneg := ratLt_to_ratLe (primeUnitRadius_pos hp) }

theorem qPrime_abs_le_unit_radius (p : Nat) (hp : IsPrime p)
    (s : RatComplex) (h : HP1WitnessRat s) :
    ratLe (qPrimeEnvelope p hp s h).absUB (primeUnitRadius p hp) :=
  ratLe_refl _

theorem qPrime_abs_lt_one (p : Nat) (hp : IsPrime p)
    (s : RatComplex) (h : HP1WitnessRat s) :
    ratLt (qPrimeEnvelope p hp s h).absUB ratOne := by
  exact primeUnitRadius_lt_one hp

structure LocalSchurContractive
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) where
  radius : Rat
  radius_nonneg : ratLe ratZero radius
  radius_lt_one : ratLt radius ratOne
  q_abs_le_radius :
    ratLe (qPrimeEnvelope p hp s h).absUB radius

def qPrime_localSchurContractive
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    LocalSchurContractive p hp s h :=
  { radius := primeUnitRadius p hp
    radius_nonneg := ratLt_to_ratLe (primeUnitRadius_pos hp)
    radius_lt_one := primeUnitRadius_lt_one hp
    q_abs_le_radius := qPrime_abs_le_unit_radius p hp s h }

structure EulerFactorBounded
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) where
  q_contracts : LocalSchurContractive p hp s h
  denominator_gap : Rat
  denominator_gap_pos : ratLt ratZero denominator_gap
  factor_bound : Rat

def primeEulerFactorBounded
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    EulerFactorBounded p hp s h :=
  let r := primeUnitRadius p hp
  let gap := ratSub ratOne r
  let hgap : ratApart0 gap :=
    ratApart0_of_pos (sub_pos_of_lt (primeUnitRadius_lt_one hp))
  { q_contracts := qPrime_localSchurContractive p hp s h
    denominator_gap := gap
    denominator_gap_pos := sub_pos_of_lt (primeUnitRadius_lt_one hp)
    factor_bound := ratDivApart ratOne gap hgap }

theorem primeEulerFactorBounded_not_scalar_contraction_claim
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    (primeEulerFactorBounded p hp s h).q_contracts.radius_lt_one =
      (qPrime_localSchurContractive p hp s h).radius_lt_one := by
  rfl

def qPrimeGeomSum
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (K : Nat) : Rat :=
  geomSum (qPrime_localSchurContractive p hp s h).radius K

theorem qPrime_geomSum_le_factor_bound
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (K : Nat) :
    ratLe (qPrimeGeomSum p hp s h K)
      (primeEulerFactorBounded p hp s h).factor_bound := by
  unfold qPrimeGeomSum primeEulerFactorBounded qPrime_localSchurContractive
  exact geomSum_le_inv_one_sub (primeUnitRadius p hp)
    (ratLt_to_ratLe (primeUnitRadius_pos hp))
    (primeUnitRadius_lt_one hp)
    K
    (ratApart0_of_pos (sub_pos_of_lt (primeUnitRadius_lt_one hp)))

def smoothUpTo (N n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, IsPrime p -> p ∣ n -> p ≤ N

def smoothSupportInWindow (W : PrimeWindow) (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, IsPrime p -> p ∣ n -> PrimeWindow.mem p W

inductive PrimeTowerFrontierBoundary where
  | alphaNegPowerMajorantNeedsLocatedExpLog
  | finiteEulerDirichletNeedsFubiniFTA
  | infiniteEulerZetaNeedsConstructivePSeriesLimit
  | criticalStripAnalyticContinuationRemains
  | terminalXiIdentificationRemains

structure FiniteEulerDirichletBoundary (N : Nat) where
  boundary : PrimeTowerFrontierBoundary
  boundary_eq :
    boundary =
      PrimeTowerFrontierBoundary.finiteEulerDirichletNeedsFubiniFTA

def finiteEulerDirichletBoundary (N : Nat) :
    FiniteEulerDirichletBoundary N :=
  { boundary := PrimeTowerFrontierBoundary.finiteEulerDirichletNeedsFubiniFTA
    boundary_eq := rfl }

structure QPrimeAlphaNegPowerMajorantBoundary
    (p : Nat) (_hp : IsPrime p) (s : RatComplex)
    (_h : HP1WitnessRat s) where
  boundary : PrimeTowerFrontierBoundary
  boundary_eq :
    boundary =
      PrimeTowerFrontierBoundary.alphaNegPowerMajorantNeedsLocatedExpLog

def qPrime_alphaNegPowerMajorantBoundary
    (p : Nat) (hp : IsPrime p) (s : RatComplex)
    (h : HP1WitnessRat s) :
    QPrimeAlphaNegPowerMajorantBoundary p hp s h :=
  { boundary :=
      PrimeTowerFrontierBoundary.alphaNegPowerMajorantNeedsLocatedExpLog
    boundary_eq := rfl }

structure FiniteEulerWindowPacket (W : PrimeWindow) (s : RatComplex)
    (h : HP1WitnessRat s) where
  local_factor_bounded :
    ∀ p : Nat, (member : PrimeWindow.mem p W) ->
      EulerFactorBounded p (All.mem W.all_prime member) s h
  smooth_support : Nat -> Prop
  smooth_support_eq :
    ∀ n : Nat, smooth_support n = smoothSupportInWindow W n
  finite_euler_dirichlet_boundary :
    FiniteEulerDirichletBoundary W.elems.length

def finiteEulerWindowPacket (W : PrimeWindow)
    (s : RatComplex) (h : HP1WitnessRat s) :
    FiniteEulerWindowPacket W s h :=
  { local_factor_bounded := fun p member =>
      primeEulerFactorBounded p (All.mem W.all_prime member) s h
    smooth_support := smoothSupportInWindow W
    smooth_support_eq := fun _n => rfl
    finite_euler_dirichlet_boundary :=
      finiteEulerDirichletBoundary W.elems.length }

structure HalfPlaneForwardPrimeDischarge (s : RatComplex)
    (h : HP1WitnessRat s) where
  local_schur :
    ∀ p : Nat, (hp : IsPrime p) ->
      LocalSchurContractive p hp s h
  local_euler_factor_bounded :
    ∀ p : Nat, (hp : IsPrime p) ->
      EulerFactorBounded p hp s h
  alpha_neg_power_majorant_boundary :
    ∀ p : Nat, (hp : IsPrime p) ->
      QPrimeAlphaNegPowerMajorantBoundary p hp s h
  finite_window_packet :
    ∀ W : PrimeWindow, FiniteEulerWindowPacket W s h
  finite_euler_dirichlet_boundary :
    ∀ N : Nat, FiniteEulerDirichletBoundary N
  critical_strip_boundary : PrimeTowerFrontierBoundary
  critical_strip_boundary_eq :
    critical_strip_boundary =
      PrimeTowerFrontierBoundary.criticalStripAnalyticContinuationRemains

def halfPlaneForwardPrimeDischarge (s : RatComplex) (h : HP1WitnessRat s) :
    HalfPlaneForwardPrimeDischarge s h :=
  { local_schur := fun p hp => qPrime_localSchurContractive p hp s h
    local_euler_factor_bounded := fun p hp => primeEulerFactorBounded p hp s h
    alpha_neg_power_majorant_boundary :=
      fun p hp => qPrime_alphaNegPowerMajorantBoundary p hp s h
    finite_window_packet := fun W => finiteEulerWindowPacket W s h
    finite_euler_dirichlet_boundary := fun N => finiteEulerDirichletBoundary N
    critical_strip_boundary :=
      PrimeTowerFrontierBoundary.criticalStripAnalyticContinuationRemains
    critical_strip_boundary_eq := rfl }

inductive HalfPlanePrimeTowerStatus where
  | localSchurKernel
  | boundedEulerFactor
  | finiteEulerDirichletBoundary
  | criticalStripBoundary
  | terminalXiBoundary

def halfPlaneStatusForPrimeTowerObligation :
    PrimeTowerFrontierObligation -> HalfPlanePrimeTowerStatus
  | PrimeTowerFrontierObligation.primeTransfer_is_JContractive =>
      HalfPlanePrimeTowerStatus.localSchurKernel
  | PrimeTowerFrontierObligation.primeTransfer_matches_Euler_event =>
      HalfPlanePrimeTowerStatus.finiteEulerDirichletBoundary
  | PrimeTowerFrontierObligation.limit_HB =>
      HalfPlanePrimeTowerStatus.criticalStripBoundary
  | PrimeTowerFrontierObligation.terminal_associatedA_eq_Xi =>
      HalfPlanePrimeTowerStatus.terminalXiBoundary

structure HalfPlanePrimeCausalTowerFrontier
    (s : RatComplex) (h : HP1WitnessRat s) where
  discharge : HalfPlaneForwardPrimeDischarge s h
  jcontractive_status : HalfPlanePrimeTowerStatus
  jcontractive_status_eq :
    jcontractive_status =
      halfPlaneStatusForPrimeTowerObligation
        PrimeTowerFrontierObligation.primeTransfer_is_JContractive
  euler_event_status : HalfPlanePrimeTowerStatus
  euler_event_status_eq :
    euler_event_status =
      halfPlaneStatusForPrimeTowerObligation
        PrimeTowerFrontierObligation.primeTransfer_matches_Euler_event
  limit_status : HalfPlanePrimeTowerStatus
  limit_status_eq :
    limit_status =
      halfPlaneStatusForPrimeTowerObligation
        PrimeTowerFrontierObligation.limit_HB
  terminal_status : HalfPlanePrimeTowerStatus
  terminal_status_eq :
    terminal_status =
      halfPlaneStatusForPrimeTowerObligation
        PrimeTowerFrontierObligation.terminal_associatedA_eq_Xi

def halfPlanePrimeCausalTowerFrontier
    (s : RatComplex) (h : HP1WitnessRat s) :
    HalfPlanePrimeCausalTowerFrontier s h :=
  { discharge := halfPlaneForwardPrimeDischarge s h
    jcontractive_status := HalfPlanePrimeTowerStatus.localSchurKernel
    jcontractive_status_eq := rfl
    euler_event_status :=
      HalfPlanePrimeTowerStatus.finiteEulerDirichletBoundary
    euler_event_status_eq := rfl
    limit_status := HalfPlanePrimeTowerStatus.criticalStripBoundary
    limit_status_eq := rfl
    terminal_status := HalfPlanePrimeTowerStatus.terminalXiBoundary
    terminal_status_eq := rfl }

def halfPlane_discharge_local_schur
    (s : RatComplex) (h : HP1WitnessRat s)
    (p : Nat) (hp : IsPrime p) :
    LocalSchurContractive p hp s h :=
  (halfPlaneForwardPrimeDischarge s h).local_schur p hp

def halfPlane_euler_factor_bounded
    (s : RatComplex) (h : HP1WitnessRat s)
    (p : Nat) (hp : IsPrime p) :
    EulerFactorBounded p hp s h :=
  (halfPlaneForwardPrimeDischarge s h).local_euler_factor_bounded p hp

def halfPlane_finiteEuler_boundary
    (s : RatComplex) (h : HP1WitnessRat s) (N : Nat) :
    FiniteEulerDirichletBoundary N :=
  (halfPlaneForwardPrimeDischarge s h).finite_euler_dirichlet_boundary N

def halfPlane_finiteEuler_window_packet
    (s : RatComplex) (h : HP1WitnessRat s) (W : PrimeWindow) :
    FiniteEulerWindowPacket W s h :=
  (halfPlaneForwardPrimeDischarge s h).finite_window_packet W

theorem critical_strip_boundary_marked
    (s : RatComplex) (h : HP1WitnessRat s) :
    (halfPlaneForwardPrimeDischarge s h).critical_strip_boundary =
      PrimeTowerFrontierBoundary.criticalStripAnalyticContinuationRemains := by
  rfl

end BEDC.Derived.RHRoute.HalfPlaneEulerProduct
