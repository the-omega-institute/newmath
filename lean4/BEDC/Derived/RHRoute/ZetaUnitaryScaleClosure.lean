import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.ZetaCosmosClosure
import BEDC.Derived.RHRoute.GoldenPowSignedExponent
import BEDC.Derived.FibonacciLucasIdentitiesUp
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete
open BEDC.Derived.RHRoute.ZetaCosmosClosure
open BEDC.Derived.RHRoute.GoldenPowSignedExponent
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.FibonacciLucasIdentitiesUp

/-
This module packages a conditional unitary-scale route.  The finite kernel is
the phi-power carrier in `Nat[phi]`: a positive phi power is the unit exactly
at exponent zero.  The analytic modulus identity and the no-independent-scale
step are explicit fields; Galperin symmetry alone is not treated as enough to
prove an RH-shaped statement.
-/

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

abbrev GoldenPow := GoldenPhiPair

def goldenPow (gamma : Nat) : GoldenPow :=
  goldenPhiPow gamma

private theorem fib_succ_pos (n : Nat) :
    0 < fib (Nat.succ n) := by
  induction n with
  | zero =>
      change 0 < 1
      exact Nat.succ_pos 0
  | succ n ih =>
      change 0 < fib (Nat.succ n) + fib n
      exact Nat.lt_of_lt_of_le ih (Nat.le_add_right (fib (Nat.succ n)) (fib n))

private theorem fib_succ_ne_zero (n : Nat) :
    fib (Nat.succ n) = 0 -> False := by
  intro h
  have hpos : 0 < fib (Nat.succ n) := fib_succ_pos n
  rw [h] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem goldenPow_succ_not_one (n : Nat) :
    goldenPow (Nat.succ n) = ⟨1, 0⟩ -> False := by
  intro h
  have pair := golden_phi_power_pair n
  have same : (⟨fib n, fib (n + 1)⟩ : GoldenPhiPair) = ⟨1, 0⟩ := by
    exact Eq.trans (Eq.symm pair) h
  have coeffZero : fib (n + 1) = 0 := by
    exact congrArg GoldenPhiPair.phiCoeff same
  exact fib_succ_ne_zero n coeffZero

theorem goldenNatPow_eq_one_iff_zero (gamma : Nat) :
    goldenPow gamma = ⟨1, 0⟩ ↔ gamma = 0 := by
  constructor
  · intro h
    cases gamma with
    | zero =>
        rfl
    | succ n =>
        exact False.elim (goldenPow_succ_not_one n h)
  · intro h
    cases h
    rfl

theorem goldenPow_eq_one_iff (gamma : Nat) :
    goldenPow gamma = ⟨1, 0⟩ ↔ gamma = 0 :=
  goldenNatPow_eq_one_iff_zero gamma

def centeredRealPart (s : RatComplex) : Rat :=
  BEDC.Derived.RationalUp.ratSub s.re halfRat

def realPartCenteredAtHalf (s : RatComplex) : Prop :=
  RatEq (centeredRealPart s) ratZero

theorem centeredExponent_eq_zero_iff_realPartCenteredAtHalf
    (s : RatComplex) :
    GoldenPowSignedExponent.GoldenPowRatEqOne
        (GoldenPowSignedExponent.goldenPowRat (centeredRealPart s)) ↔
      realPartCenteredAtHalf s := by
  exact GoldenPowSignedExponent.goldenPowRat_eq_one_iff
    (centeredRealPart s)

structure NoIndependentRealScale (s : RatComplex) where
  zero_point : NontrivialZetaZero s
  ledger_channel : Nat

structure CenteredGoldenScale (s : RatComplex) where
  exponentCode : Rat
  modulus : Rat
  golden_power : GoldenPowRat
  golden_power_readback :
    golden_power = goldenPowRat exponentCode
  exponent_reads_centered_real :
    RatEq exponentCode (centeredRealPart s)
  centered_real_reads_exponent :
    RatEq (centeredRealPart s) ratZero -> RatEq exponentCode ratZero
  unit_modulus_reads_golden_unit :
    RatEq modulus ratOne -> GoldenPowRatEqOne golden_power
  golden_unit_reads_unit_modulus :
    GoldenPowRatEqOne golden_power -> RatEq modulus ratOne

structure ZetaUnitaryScaleClosure where
  scale_eigenvalue :
    (s : RatComplex) ->
      NontrivialZetaZero s -> CenteredGoldenScale s
  modulus_identity :
    (s : RatComplex) -> (zero : NontrivialZetaZero s) ->
      (scale_eigenvalue s zero).golden_power =
        goldenPowRat (scale_eigenvalue s zero).exponentCode
  unitary_from_no_scale :
    (s : RatComplex) -> (zero : NontrivialZetaZero s) ->
      NoIndependentRealScale s ->
        RatEq (scale_eigenvalue s zero).modulus ratOne
  no_scale_for_zero :
    (s : RatComplex) -> (zero : NontrivialZetaZero s) ->
      NoIndependentRealScale s

def ZetaCosmosNoScaleLedgerLinked
    {signature : BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature}
    {unfolding : ZetaGalperinInertialUnfolding signature}
    (_cosmos : ZetaCosmosClosure unfolding)
    (closure : ZetaUnitaryScaleClosure) : Prop :=
  NoIndependentRealScaleLedger unfolding ∧
    (∀ s : RatComplex, (zero : NontrivialZetaZero s) ->
      (closure.no_scale_for_zero s zero).ledger_channel =
        0) ∧
    (∀ s : RatComplex, (zero : NontrivialZetaZero s) ->
      (closure.scale_eigenvalue s zero).golden_power =
        goldenPowRat (closure.scale_eigenvalue s zero).exponentCode)

theorem zetaCosmosNoScaleLedgerLinked_intro
    {signature : BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature}
    {unfolding : ZetaGalperinInertialUnfolding signature}
    (cosmos : ZetaCosmosClosure unfolding)
    (closure : ZetaUnitaryScaleClosure)
    (channel_reads :
      ∀ s : RatComplex, (zero : NontrivialZetaZero s) ->
        (closure.no_scale_for_zero s zero).ledger_channel =
          0)
    (power_reads :
      ∀ s : RatComplex, (zero : NontrivialZetaZero s) ->
        (closure.scale_eigenvalue s zero).golden_power =
          goldenPowRat (closure.scale_eigenvalue s zero).exponentCode) :
    ZetaCosmosNoScaleLedgerLinked cosmos closure := by
  exact ⟨cosmos.no_independent_real_scale_ledger, channel_reads, power_reads⟩

theorem unitary_scale_closure_zero_re_centered
    (closure : ZetaUnitaryScaleClosure)
    (s : RatComplex) (zero : NontrivialZetaZero s) :
    realPartCenteredAtHalf s := by
  let scale := closure.scale_eigenvalue s zero
  have hmod : RatEq scale.modulus ratOne :=
    closure.unitary_from_no_scale s zero
      (closure.no_scale_for_zero s zero)
  have hgoldenUnit : GoldenPowRatEqOne scale.golden_power :=
    scale.unit_modulus_reads_golden_unit hmod
  have hpow : GoldenPowRatEqOne (goldenPowRat scale.exponentCode) := by
    rw [← closure.modulus_identity s zero]
    exact hgoldenUnit
  have hcode : RatEq scale.exponentCode ratZero :=
    (goldenPowRat_eq_one_iff scale.exponentCode).mp hpow
  have hcenter : RatEq (centeredRealPart s) ratZero :=
    RatEq_trans _ _ _ (RatEq_symm scale.exponent_reads_centered_real) hcode
  exact hcenter

theorem scale_unit_modulus_iff_centered_real
    (closure : ZetaUnitaryScaleClosure)
    (s : RatComplex) (zero : NontrivialZetaZero s) :
    RatEq (closure.scale_eigenvalue s zero).modulus ratOne ↔
      realPartCenteredAtHalf s := by
  constructor
  · intro hmod
    let scale := closure.scale_eigenvalue s zero
    have hgoldenUnit : GoldenPowRatEqOne scale.golden_power :=
      scale.unit_modulus_reads_golden_unit hmod
    have hpow : GoldenPowRatEqOne (goldenPowRat scale.exponentCode) := by
      rw [← closure.modulus_identity s zero]
      exact hgoldenUnit
    have hcode : RatEq scale.exponentCode ratZero :=
      (goldenPowRat_eq_one_iff scale.exponentCode).mp hpow
    exact RatEq_trans _ _ _ (RatEq_symm scale.exponent_reads_centered_real) hcode
  · intro hcenter
    let scale := closure.scale_eigenvalue s zero
    have hcode : RatEq scale.exponentCode ratZero :=
      scale.centered_real_reads_exponent hcenter
    have hpow : GoldenPowRatEqOne (goldenPowRat scale.exponentCode) :=
      (goldenPowRat_eq_one_iff scale.exponentCode).mpr hcode
    have hgoldenUnit : GoldenPowRatEqOne scale.golden_power := by
      rw [closure.modulus_identity s zero]
      exact hpow
    exact scale.golden_unit_reads_unit_modulus hgoldenUnit

theorem scale_unit_modulus_iff_re_half
    (closure : ZetaUnitaryScaleClosure)
    (s : RatComplex) (zero : NontrivialZetaZero s) :
    RatEq (closure.scale_eigenvalue s zero).modulus ratOne ↔
      RatEq s.re halfRat := by
  exact Iff.trans (scale_unit_modulus_iff_centered_real closure s zero)
    (BEDC.Derived.RationalUp.ratSub_zero_iff s.re halfRat)

theorem realPartCenteredAtHalf_reads_onCriticalLine
    {s : RatComplex} :
    realPartCenteredAtHalf s -> OnCriticalLine s := by
  intro h
  exact (BEDC.Derived.RationalUp.ratSub_zero_iff s.re halfRat).mp h

theorem rh_via_unitary_scale_closure
    (closure : ZetaUnitaryScaleClosure) :
    ConstructiveRH := by
  intro s zero
  exact realPartCenteredAtHalf_reads_onCriticalLine
    (unitary_scale_closure_zero_re_centered closure s zero)

end BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure
