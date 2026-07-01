import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.GoldenPowSignedExponent

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.IntUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLtBool_true_to_ratLt_local {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt intLtUp intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le_local h)

def goldenLower : Rat :=
  ratDivApart (ratNat 8) (ratNat 5)
    (ratNat_apart0_of_pos (Nat.succ_pos 4))

def goldenUpper : Rat :=
  ratDivApart (ratNat 13) (ratNat 8)
    (ratNat_apart0_of_pos (Nat.succ_pos 7))

structure GoldenLocated where
  lower : Rat
  upper : Rat
  one_lt_lower : ratLt ratOne lower
  lower_lt_upper : ratLt lower upper
  upper_lt_two : ratLt upper ratTwo
  lower_square_lt_shift : ratLt (ratMul lower lower) (ratAdd lower ratOne)
  shift_lt_upper_square : ratLt (ratAdd upper ratOne) (ratMul upper upper)

def goldenPhiLocated : GoldenLocated :=
  { lower := goldenLower
    upper := goldenUpper
    one_lt_lower := by
      unfold goldenLower
      exact ratLtBool_true_to_ratLt_local (by rfl)
    lower_lt_upper := by
      unfold goldenLower goldenUpper
      exact ratLtBool_true_to_ratLt_local (by rfl)
    upper_lt_two := by
      unfold goldenUpper
      exact ratLtBool_true_to_ratLt_local (by rfl)
    lower_square_lt_shift := by
      unfold goldenLower
      exact ratLtBool_true_to_ratLt_local (by rfl)
    shift_lt_upper_square := by
      unfold goldenUpper
      exact ratLtBool_true_to_ratLt_local (by rfl) }

structure GoldenPowRat where
  exponent : Rat
  phi : GoldenLocated

def goldenPowRat (gamma : Rat) : GoldenPowRat :=
  { exponent := gamma
    phi := goldenPhiLocated }

def GoldenPowRatAboveOne (x : GoldenPowRat) : Prop :=
  ratLt ratZero x.exponent ∧ ratLt ratOne x.phi.lower

def GoldenPowRatBelowOne (x : GoldenPowRat) : Prop :=
  ratLt x.exponent ratZero ∧ ratLt ratOne x.phi.lower

inductive GoldenPowRatApartOne (x : GoldenPowRat) : Prop where
  | above : GoldenPowRatAboveOne x -> GoldenPowRatApartOne x
  | below : GoldenPowRatBelowOne x -> GoldenPowRatApartOne x

def GoldenPowRatEqOne (x : GoldenPowRat) : Prop :=
  GoldenPowRatApartOne x -> False

private theorem ratPos_not_eq_zero {gamma : Rat} :
    ratLt ratZero gamma -> RatEq gamma ratZero -> False := by
  intro hpos hzero
  exact ratLt_not_RatEq hpos (RatEq_symm hzero)

private theorem ratNeg_not_eq_zero {gamma : Rat} :
    ratLt gamma ratZero -> RatEq gamma ratZero -> False := by
  intro hneg hzero
  exact ratLt_not_RatEq hneg hzero

theorem goldenPowRat_positive_above_one {gamma : Rat} :
    ratLt ratZero gamma -> GoldenPowRatAboveOne (goldenPowRat gamma) := by
  intro hpos
  exact ⟨hpos, goldenPhiLocated.one_lt_lower⟩

theorem goldenPowRat_negative_below_one {gamma : Rat} :
    ratLt gamma ratZero -> GoldenPowRatBelowOne (goldenPowRat gamma) := by
  intro hneg
  exact ⟨hneg, goldenPhiLocated.one_lt_lower⟩

theorem goldenPowRat_zero_eq_one :
    GoldenPowRatEqOne (goldenPowRat ratZero) := by
  intro h
  cases h with
  | above hAbove =>
      exact ratLt_irrefl ratZero hAbove.left
  | below hBelow =>
      exact ratLt_irrefl ratZero hBelow.left

theorem goldenPowRat_eq_one_iff (gamma : Rat) :
    GoldenPowRatEqOne (goldenPowRat gamma) ↔ RatEq gamma ratZero := by
  constructor
  · intro hunit
    cases rat_order_trichotomy gamma ratZero with
    | inl gammaNeg =>
        exact False.elim
          (hunit
            (GoldenPowRatApartOne.below
              (goldenPowRat_negative_below_one gammaNeg)))
    | inr rest =>
        cases rest with
        | inl gammaZero =>
            exact gammaZero
        | inr zeroLtGamma =>
            exact False.elim
              (hunit
                (GoldenPowRatApartOne.above
                  (goldenPowRat_positive_above_one zeroLtGamma)))
  · intro hzero
    intro h
    cases h with
    | above hpos =>
        exact ratPos_not_eq_zero hpos.left hzero
    | below hneg =>
        exact ratNeg_not_eq_zero hneg.left hzero

theorem goldenPowRat_eq_one_iff_signed (gamma : Rat) :
    GoldenPowRatEqOne (goldenPowRat gamma) ↔ RatEq gamma ratZero :=
  goldenPowRat_eq_one_iff gamma

def centeredExponentOfRealPart (re : Rat) : Rat :=
  ratSub re BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat

theorem centeredExponent_eq_zero_iff_re_half (re : Rat) :
    RatEq (centeredExponentOfRealPart re) ratZero ↔
      RatEq re BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat :=
  BEDC.Derived.RationalUp.ratSub_zero_iff re
    BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat

end BEDC.Derived.RHRoute.GoldenPowSignedExponent
