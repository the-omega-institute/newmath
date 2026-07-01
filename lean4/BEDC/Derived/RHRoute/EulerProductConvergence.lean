import BEDC.Derived.RHRoute.QPrimeLocated
import BEDC.Derived.RHRoute.FiniteEulerDirichlet

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.EulerProductConvergence

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.HalfPlaneEulerProduct
open BEDC.Derived.RHRoute.QPrimeLocated
open BEDC.Derived.RHRoute.FiniteEulerDirichlet
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  HalfPlaneEulerProduct.Rat

abbrev RatComplex : Type :=
  HalfPlaneEulerProduct.RatComplex

def pSeriesTailWindow (a : Nat -> Rat) (N : Nat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ K =>
      ratAdd (pSeriesTailWindow a N K) (a (N + K))

def geometricTailBound
    (q : Rat) (hq1 : ratLt q ratOne) (N : Nat) : Rat :=
  ratDivApart (ratPow q N) (ratSub ratOne q)
    (ratApart0_of_pos (sub_pos_of_lt hq1))

theorem pSeriesTailWindow_geometric_eq
    (q : Rat) (N K : Nat) :
    RatEq (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
      (ratMul (ratPow q N) (geomSum q K)) := by
  induction K with
  | zero =>
      change RatEq ratZero (ratMul (ratPow q N) ratZero)
      exact RatEq_symm
        (ratMul_sum_left (ratPow q N) 0 (fun j : Nat => ratPow q j))
  | succ K ih =>
      change
        RatEq
          (ratAdd (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
            (ratPow q (N + K)))
          (ratMul (ratPow q N)
            (ratAdd (geomSum q K) (ratPow q K)))
      have leftToExpanded :
          RatEq
            (ratAdd (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
              (ratPow q (N + K)))
            (ratAdd (ratMul (ratPow q N) (geomSum q K))
              (ratMul (ratPow q N) (ratPow q K))) :=
        ratAdd_respects ih (ratPow_add q N K)
      have expandedToRight :
          RatEq
            (ratAdd (ratMul (ratPow q N) (geomSum q K))
              (ratMul (ratPow q N) (ratPow q K)))
            (ratMul (ratPow q N)
              (ratAdd (geomSum q K) (ratPow q K))) :=
        RatEq_symm
          (ratMul_add_left (ratPow q N) (geomSum q K) (ratPow q K))
      exact RatEq_trans _ _ _ leftToExpanded expandedToRight

private theorem geometricTailBound_scaled_inverse
    (q : Rat) (hq1 : ratLt q ratOne) (N : Nat) :
    RatEq
      (ratMul (ratPow q N)
        (ratDivApart ratOne (ratSub ratOne q)
          (ratApart0_of_pos (sub_pos_of_lt hq1))))
      (geometricTailBound q hq1 N) := by
  unfold geometricTailBound ratDivApart
  exact ratMul_respects (RatEq_refl (ratPow q N))
    (ratOne_mul_left
      (ratInvApart (ratSub ratOne q)
        (ratApart0_of_pos (sub_pos_of_lt hq1))))

theorem geometric_p_series_tail_bound
    (q : Rat)
    (hq0 : ratLe ratZero q)
    (hq1 : ratLt q ratOne)
    (N K : Nat) :
    ratLe (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
      (geometricTailBound q hq1 N) := by
  let gapApart := ratApart0_of_pos (sub_pos_of_lt hq1)
  have geomLe :
      ratLe (geomSum q K)
        (ratDivApart ratOne (ratSub ratOne q) gapApart) :=
    geomSum_le_inv_one_sub q hq0 hq1 K gapApart
  have scaleNonneg : ratLe ratZero (ratPow q N) :=
    ratPow_nonneg hq0 N
  have scaled :
      ratLe
        (ratMul (ratPow q N) (geomSum q K))
        (ratMul (ratPow q N)
          (ratDivApart ratOne (ratSub ratOne q) gapApart)) :=
    ratMul_le_mul_nonneg_left geomLe scaleNonneg
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left
      (pSeriesTailWindow_geometric_eq q N K)
      scaled)
    (geometricTailBound_scaled_inverse q hq1 N)

theorem pSeriesTailWindow_scale_eq
    (c : Rat) (a : Nat -> Rat) (N K : Nat) :
    RatEq (pSeriesTailWindow (fun n : Nat => ratMul c (a n)) N K)
      (ratMul c (pSeriesTailWindow a N K)) := by
  induction K with
  | zero =>
      change RatEq ratZero (ratMul c ratZero)
      exact RatEq_symm (ratMul_sum_left c 0 a)
  | succ K ih =>
      change
        RatEq
          (ratAdd
            (pSeriesTailWindow (fun n : Nat => ratMul c (a n)) N K)
            (ratMul c (a (N + K))))
          (ratMul c (ratAdd (pSeriesTailWindow a N K) (a (N + K))))
      have leftToExpanded :
          RatEq
            (ratAdd
              (pSeriesTailWindow (fun n : Nat => ratMul c (a n)) N K)
              (ratMul c (a (N + K))))
            (ratAdd
              (ratMul c (pSeriesTailWindow a N K))
              (ratMul c (a (N + K)))) :=
        ratAdd_respects ih (RatEq_refl (ratMul c (a (N + K))))
      have expandedToRight :
          RatEq
            (ratAdd
              (ratMul c (pSeriesTailWindow a N K))
              (ratMul c (a (N + K))))
            (ratMul c (ratAdd (pSeriesTailWindow a N K) (a (N + K)))) :=
        RatEq_symm
          (ratMul_add_left c (pSeriesTailWindow a N K) (a (N + K)))
      exact RatEq_trans _ _ _ leftToExpanded expandedToRight

theorem geometric_log_tail_bound
    (q : Rat)
    (hq0 : ratLe ratZero q)
    (hq1 : ratLt q ratOne)
    (N K : Nat) :
    ratLe
      (pSeriesTailWindow (fun n : Nat => ratMul ratTwo (ratPow q n)) N K)
      (ratMul ratTwo (geometricTailBound q hq1 N)) := by
  have raw :
      ratLe (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
        (geometricTailBound q hq1 N) :=
    geometric_p_series_tail_bound q hq0 hq1 N K
  exact ratLe_of_RatEq_left
    (pSeriesTailWindow_scale_eq ratTwo (fun n : Nat => ratPow q n) N K)
    (ratMul_le_mul_nonneg_left raw ratTwo_nonneg)

structure GeometricTailKernel where
  q : Rat
  q_nonneg : ratLe ratZero q
  q_lt_one : ratLt q ratOne
  tail_bound :
    forall N K : Nat,
      ratLe (pSeriesTailWindow (fun n : Nat => ratPow q n) N K)
        (geometricTailBound q q_lt_one N)

structure PSeriesTailLocated
    (s : RatComplex) (h : HP1WitnessRat s) where
  alpha : Rat
  alpha_eq : alpha = h.alpha
  alpha_gt_one : ratLt ratOne alpha
  re_ge_alpha : ratLe alpha s.re
  majorant : Nat -> Rat
  majorant_nonneg : forall n : Nat, ratLe ratZero (majorant n)
  tail_bound : Nat -> Rat
  tail_bound_nonneg : forall N : Nat, ratLe ratZero (tail_bound N)
  explicit_modulus : Rat -> Nat
  tail_le_modulus :
    forall eps : Rat, ratLt ratZero eps ->
      ratLe (tail_bound (explicit_modulus eps)) eps
  p_series_tail_bound :
    forall N K : Nat,
      ratLe (pSeriesTailWindow majorant N K) (tail_bound N)
  geometric_kernel : GeometricTailKernel

theorem p_series_tail_bound_re_gt_one
    {s : RatComplex} {h : HP1WitnessRat s}
    (tail : PSeriesTailLocated s h) :
    forall N K : Nat,
      ratLe (pSeriesTailWindow tail.majorant N K) (tail.tail_bound N) := by
  exact tail.p_series_tail_bound

def p_series_tail_geometric_kernel
    {s : RatComplex} {h : HP1WitnessRat s}
    (tail : PSeriesTailLocated s h) :
    GeometricTailKernel := by
  exact tail.geometric_kernel

theorem p_series_tail_modulus_sound
    {s : RatComplex} {h : HP1WitnessRat s}
    (tail : PSeriesTailLocated s h) :
    forall eps : Rat, ratLt ratZero eps ->
      ratLe (tail.tail_bound (tail.explicit_modulus eps)) eps := by
  exact tail.tail_le_modulus

structure EulerPartialProductLocated
    (s : RatComplex) (h : HP1WitnessRat s) (N : Nat) where
  cutoff : Nat
  cutoff_eq : cutoff = N
  value : RatComplex
  local_factor :
    forall p : Nat, p <= N -> (hp : IsPrime p) ->
      QPrimeLocated p hp s h
  envelope_radius : Rat
  envelope_radius_nonneg : ratLe ratZero envelope_radius

def eulerPartialProductValue
    {s : RatComplex} {h : HP1WitnessRat s} {N : Nat}
    (P : EulerPartialProductLocated s h N) : RatComplex :=
  P.value

structure EulerPartialProductDistanceEnvelope
    {s : RatComplex} {h : HP1WitnessRat s}
    (partials : forall N : Nat, EulerPartialProductLocated s h N)
    (tail : PSeriesTailLocated s h) where
  distanceUB : Nat -> Nat -> Rat
  distanceUB_nonneg :
    forall M N : Nat, ratLe ratZero (distanceUB M N)
  distance_le_tail :
    forall M N : Nat, N <= M ->
      ratLe (distanceUB M N) (tail.tail_bound N)
  product_tail_sources :
    forall M N : Nat, N <= M ->
      ratLe (pSeriesTailWindow tail.majorant N (M - N))
        (tail.tail_bound N)

structure EulerProductReGtOnePacket
    (s : RatComplex) (h : HP1WitnessRat s) where
  tail : PSeriesTailLocated s h
  partials : forall N : Nat, EulerPartialProductLocated s h N
  distance :
    EulerPartialProductDistanceEnvelope partials tail
  obligation : EffectiveConvergenceObligation
  obligation_eq : obligation = infiniteEulerZetaConvergenceObligation

def EulerPartialProductLocatedCauchy
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) : Prop :=
  forall eps : Rat, ratLt ratZero eps ->
    Exists fun N : Nat =>
      forall M : Nat, N <= M ->
        ratLe (packet.distance.distanceUB M N) eps

theorem eulerPartialProduct_explicit_modulus
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) :
    forall eps : Rat, ratLt ratZero eps ->
      forall M : Nat, packet.tail.explicit_modulus eps <= M ->
        ratLe
          (packet.distance.distanceUB M
            (packet.tail.explicit_modulus eps))
          eps := by
  intro eps eps_pos M hM
  exact ratLe_trans
    (packet.distance.distance_le_tail M
      (packet.tail.explicit_modulus eps) hM)
    (packet.tail.tail_le_modulus eps eps_pos)

theorem eulerPartialProduct_located_cauchy
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) :
    EulerPartialProductLocatedCauchy packet := by
  intro eps eps_pos
  exact Exists.intro (packet.tail.explicit_modulus eps)
    (eulerPartialProduct_explicit_modulus packet eps eps_pos)

inductive EulerProductConvergenceBoundary where
  | reGtOneLocatedEulerProduct
  | criticalStripAnalyticContinuationHardCore

structure EulerProductEffectiveConvergenceReGtOne
    (s : RatComplex) (h : HP1WitnessRat s) where
  packet : EulerProductReGtOnePacket s h
  cauchy :
    EulerPartialProductLocatedCauchy packet
  effective_modulus : Rat -> Nat
  effective_modulus_eq :
    effective_modulus = packet.tail.explicit_modulus
  obligation :
    EffectiveConvergenceObligation
  obligation_eq :
    obligation = infiniteEulerZetaConvergenceObligation
  re_gt_one_boundary : EulerProductConvergenceBoundary
  re_gt_one_boundary_eq :
    re_gt_one_boundary =
      EulerProductConvergenceBoundary.reGtOneLocatedEulerProduct
  critical_strip_boundary : EulerProductConvergenceBoundary
  critical_strip_boundary_eq :
    critical_strip_boundary =
      EulerProductConvergenceBoundary.criticalStripAnalyticContinuationHardCore
  half_plane_boundary_readback :
    (halfPlaneForwardPrimeDischarge s h).critical_strip_boundary =
      PrimeTowerFrontierBoundary.criticalStripAnalyticContinuationRemains

def eulerProduct_effective_convergence_re_gt_one_certificate
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) :
    EulerProductEffectiveConvergenceReGtOne s h := by
  exact
    { packet := packet
      cauchy := eulerPartialProduct_located_cauchy packet
      effective_modulus := packet.tail.explicit_modulus
      effective_modulus_eq := rfl
      obligation := packet.obligation
      obligation_eq := packet.obligation_eq
      re_gt_one_boundary :=
        EulerProductConvergenceBoundary.reGtOneLocatedEulerProduct
      re_gt_one_boundary_eq := rfl
      critical_strip_boundary :=
        EulerProductConvergenceBoundary.criticalStripAnalyticContinuationHardCore
      critical_strip_boundary_eq := rfl
      half_plane_boundary_readback := rfl }

theorem eulerProduct_effective_convergence_re_gt_one
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) :
    Exists fun cert : EulerProductEffectiveConvergenceReGtOne s h =>
      cert.packet = packet ∧
        EulerPartialProductLocatedCauchy packet ∧
          cert.critical_strip_boundary =
            EulerProductConvergenceBoundary.criticalStripAnalyticContinuationHardCore := by
  exact
    Exists.intro
      (eulerProduct_effective_convergence_re_gt_one_certificate packet)
      (And.intro rfl
        (And.intro
          (eulerPartialProduct_located_cauchy packet)
          rfl))

theorem critical_strip_marked_hardcore
    {s : RatComplex} {h : HP1WitnessRat s}
    (packet : EulerProductReGtOnePacket s h) :
    (eulerProduct_effective_convergence_re_gt_one_certificate packet).critical_strip_boundary =
      EulerProductConvergenceBoundary.criticalStripAnalyticContinuationHardCore := by
  rfl

def toyTailBound (_N : Nat) : Rat :=
  ratZero

def toyExplicitModulus (_eps : Rat) : Nat :=
  10

theorem toy_pSeriesTailWindow_zero_majorant_le_zero :
    forall N K : Nat,
      ratLe (pSeriesTailWindow (fun _n : Nat => ratZero) N K) ratZero
  | _N, 0 => ratLe_refl ratZero
  | N, Nat.succ K => by
      change
        ratLe
          (ratAdd (pSeriesTailWindow (fun _n : Nat => ratZero) N K)
            ratZero)
          ratZero
      have addBound :
          ratLe
            (ratAdd (pSeriesTailWindow (fun _n : Nat => ratZero) N K)
              ratZero)
            (ratAdd ratZero ratZero) :=
        ratAdd_le_add
          (toy_pSeriesTailWindow_zero_majorant_le_zero N K)
          (ratLe_refl ratZero)
      exact ratLe_of_RatEq_right addBound (ratAdd_zero_right ratZero)

def toyPSeriesTailLocated :
    PSeriesTailLocated toyTwoPoint toyHP1 :=
  { alpha := toyHP1.alpha
    alpha_eq := rfl
    alpha_gt_one := toyHP1.h_alpha_gt_one
    re_ge_alpha := toyHP1.h_re_ge_alpha
    majorant := fun _n => ratZero
    majorant_nonneg := fun _n => ratLe_refl ratZero
    tail_bound := toyTailBound
    tail_bound_nonneg := fun _N =>
      ratLe_refl ratZero
    explicit_modulus := toyExplicitModulus
    tail_le_modulus := by
      intro eps eps_pos
      unfold toyTailBound
      exact ratLt_to_ratLe eps_pos
    p_series_tail_bound := by
      intro N K
      exact toy_pSeriesTailWindow_zero_majorant_le_zero N K
    geometric_kernel :=
      { q := toyQuarter
        q_nonneg := toyQuarter_nonneg
        q_lt_one := toyQuarter_lt_one
        tail_bound := by
          intro N K
          exact geometric_p_series_tail_bound toyQuarter
            toyQuarter_nonneg toyQuarter_lt_one N K } }

def toyPrimeUnitRadialLocated
    (p : Nat) (hp : IsPrime p) :
    QPrimeRadialLocated p hp toyTwoPoint :=
  { exp_input := qPrimeExpInput p toyTwoPoint
    exp_input_eq := rfl
    radius := primeUnitRadius p hp
    radius_nonneg := ratLt_to_ratLe (primeUnitRadius_pos hp)
    radius_lt_one := primeUnitRadius_lt_one hp
    unit_majorant := ratLe_refl (primeUnitRadius p hp)
    log_enclosure :=
      BEDC.Real.RatNumLogEnclosure.formal_lnN_enclosure p
        (BEDC.Real.RatNumLogEnclosure.lnM96 p)
        (Nat.le_of_lt (prime_nat_gt_one hp))
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.halfPlaneUnitMajorant ]
    bridge_obligations_eq := rfl }

def toyPrimeUnitPhaseLocated
    (p : Nat) :
    QPrimePhaseLocated p toyTwoPoint :=
  { phase := qPrimePhaseCenter p toyTwoPoint
    phase_eq := rfl
    cos := qPoint ratOne
    sin := qPoint ratZero
    cos_ordered := qPoint_ordered ratOne
    sin_ordered := qPoint_ordered ratZero
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase ]
    bridge_obligations_eq := rfl }

def toyPrimeUnitQPrimeLocated
    (p : Nat) (hp : IsPrime p) :
    QPrimeLocated p hp toyTwoPoint toyHP1 :=
  assembleQPrimeLocated
    (toyPrimeUnitRadialLocated p hp)
    (toyPrimeUnitPhaseLocated p)

def toyEulerPartialProductLocated (N : Nat) :
    EulerPartialProductLocated toyTwoPoint toyHP1 N :=
  { cutoff := N
    cutoff_eq := rfl
    value := FiniteEulerDirichlet.unitComplex
    local_factor := by
      intro p _pLeN hp
      exact toyPrimeUnitQPrimeLocated p hp
    envelope_radius := ratOne
    envelope_radius_nonneg :=
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

def toyEulerDistanceEnvelope :
    EulerPartialProductDistanceEnvelope
      toyEulerPartialProductLocated toyPSeriesTailLocated :=
  { distanceUB := fun _M _N => ratZero
    distanceUB_nonneg := fun _M _N => ratLe_refl ratZero
    distance_le_tail := by
      intro _M N _hNM
      unfold toyPSeriesTailLocated toyTailBound
      exact ratLe_refl ratZero
    product_tail_sources := by
      intro M N _hNM
      exact toy_pSeriesTailWindow_zero_majorant_le_zero N (M - N) }

def toyEulerProductReGtOnePacket :
    EulerProductReGtOnePacket toyTwoPoint toyHP1 :=
  { tail := toyPSeriesTailLocated
    partials := toyEulerPartialProductLocated
    distance := toyEulerDistanceEnvelope
    obligation := infiniteEulerZetaConvergenceObligation
    obligation_eq := rfl }

structure ToyEulerProductConvergenceWitness where
  point : RatComplex
  point_eq : point = toyTwoPoint
  cutoff : Nat
  cutoff_eq : cutoff = 10
  partialProduct :
    EulerPartialProductLocated toyTwoPoint toyHP1 cutoff
  partial_cutoff_eq : partialProduct.cutoff = 10
  modulus_at_one : Nat
  modulus_at_one_eq :
    modulus_at_one =
      toyEulerProductReGtOnePacket.tail.explicit_modulus ratOne
  cauchy_at_one :
    forall M : Nat, modulus_at_one <= M ->
      ratLe
        (toyEulerProductReGtOnePacket.distance.distanceUB M
          modulus_at_one)
        ratOne
  geometric_tail_at_ten :
    forall K : Nat,
      ratLe
        (pSeriesTailWindow (fun n : Nat => ratPow toyQuarter n) 10 K)
        (geometricTailBound toyQuarter toyQuarter_lt_one 10)
  log_tail_at_ten :
    forall K : Nat,
      ratLe
        (pSeriesTailWindow
          (fun n : Nat => ratMul ratTwo (ratPow toyQuarter n)) 10 K)
        (ratMul ratTwo
          (geometricTailBound toyQuarter toyQuarter_lt_one 10))
  located_factor_at_two :
    QPrimeLocated 2 QPrimeLocated.two_isPrime toyTwoPoint toyHP1
  located_factor_at_two_abs :
    qPrimeLocatedAbs located_factor_at_two = toyQuarter
  critical_strip_boundary :
    (eulerProduct_effective_convergence_re_gt_one_certificate
      toyEulerProductReGtOnePacket).critical_strip_boundary =
      EulerProductConvergenceBoundary.criticalStripAnalyticContinuationHardCore

def toy_s_eq_two_N10_partial_product_located_convergence :
    ToyEulerProductConvergenceWitness :=
  { point := toyTwoPoint
    point_eq := rfl
    cutoff := 10
    cutoff_eq := rfl
    partialProduct := toyEulerPartialProductLocated 10
    partial_cutoff_eq := rfl
    modulus_at_one :=
      toyEulerProductReGtOnePacket.tail.explicit_modulus ratOne
    modulus_at_one_eq := rfl
    cauchy_at_one := by
      intro M hM
      exact eulerPartialProduct_explicit_modulus
        toyEulerProductReGtOnePacket ratOne
        BEDC.Real.RatNumLogEnclosure.ratOne_pos M hM
    geometric_tail_at_ten := by
      intro K
      exact geometric_p_series_tail_bound toyQuarter
        toyQuarter_nonneg toyQuarter_lt_one 10 K
    log_tail_at_ten := by
      intro K
      exact geometric_log_tail_bound toyQuarter
        toyQuarter_nonneg toyQuarter_lt_one 10 K
    located_factor_at_two := qPrimeLocatedToyTwoAtTwo
    located_factor_at_two_abs := toy_qPrimeLocated_abs_eq_quarter
    critical_strip_boundary := rfl }

theorem toy_witness_cutoff_ten :
    toy_s_eq_two_N10_partial_product_located_convergence.cutoff = 10 := by
  exact toy_s_eq_two_N10_partial_product_located_convergence.cutoff_eq

theorem toy_witness_modulus_one_ten :
    toy_s_eq_two_N10_partial_product_located_convergence.modulus_at_one = 10 := by
  exact toy_s_eq_two_N10_partial_product_located_convergence.modulus_at_one_eq

theorem toy_witness_factor_two_abs_quarter :
    qPrimeLocatedAbs
      toy_s_eq_two_N10_partial_product_located_convergence.located_factor_at_two =
      toyQuarter := by
  rfl

theorem toy_witness_geometric_tail_at_ten :
    forall K : Nat,
      ratLe
        (pSeriesTailWindow (fun n : Nat => ratPow toyQuarter n) 10 K)
        (geometricTailBound toyQuarter toyQuarter_lt_one 10) := by
  exact toy_s_eq_two_N10_partial_product_located_convergence.geometric_tail_at_ten

theorem toy_witness_log_tail_at_ten :
    forall K : Nat,
      ratLe
        (pSeriesTailWindow
          (fun n : Nat => ratMul ratTwo (ratPow toyQuarter n)) 10 K)
        (ratMul ratTwo
          (geometricTailBound toyQuarter toyQuarter_lt_one 10)) := by
  exact toy_s_eq_two_N10_partial_product_located_convergence.log_tail_at_ten

end BEDC.Derived.RHRoute.EulerProductConvergence
