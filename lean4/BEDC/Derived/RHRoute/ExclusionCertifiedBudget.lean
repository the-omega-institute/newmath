import BEDC.Derived.RHRoute.HerglotzKernelPositivity
import BEDC.Derived.RHRoute.ThreeFourOneSOS

namespace BEDC.Derived.RHRoute.ExclusionCertifiedBudget

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

abbrev natRat (n : Nat) : Rat :=
  BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat n

def dvpBudget (A B C : Rat) : Rat :=
  ratAdd (ratAdd (ratMul (natRat 3) A) (ratMul (natRat 4) B)) C

def concreteHerglotzSpectralAmount : Rat :=
  ratAdd
    (ratMul
      (ratSub
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratTwoH
        ratHalf)
      (ratSub
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratTwoH
        ratHalf))
    (ratMul
      (ratSub
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratFourteen
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratFourteen)
      (ratSub
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratFourteen
        BEDC.Derived.RHRoute.HerglotzKernelPositivity.ratFourteen))

private theorem natRat_nonneg_local (n : Nat) :
    ratLe ratZero (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumKernel.ratNat_nonneg n

private theorem natRat_pos_local {n : Nat} (h : 0 < n) :
    ratLt ratZero (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  change ratLt (ratNat 0) (ratNat n)
  exact BEDC.Real.RatNumLogEnclosure.ratNat_lt_of_nat_lt h

private theorem ratAdd_nonneg_local {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratLe_add_nonneg_right_local (x y : Rat) :
    ratLe ratZero y -> ratLe x (ratAdd x y) := by
  intro hy
  have raw :
      ratLe (ratAdd x ratZero) (ratAdd x y) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (y := ratZero) (y' := y) (x := x) hy
  exact ratLe_respects (ratAdd_zero_right x) (RatEq_refl _) raw

private theorem ratAdd_pos_of_pos_nonneg_local {x y : Rat} :
    ratLt ratZero x -> ratLe ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro hx hy
  apply ratLe_not_le_to_ratLt
  · exact ratAdd_nonneg_local (ratLt_to_ratLe hx) hy
  · intro sumLeZero
    have xLeSum : ratLe x (ratAdd x y) :=
      ratLe_add_nonneg_right_local x y hy
    exact ratLt_not_ratLe_reverse hx (ratLe_trans xLeSum sumLeZero)

private theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro xPos yPos
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left yPos xPos
  exact ratLt_respects_local (ratMul_zero_right_local x) (RatEq_refl _) raw

private theorem concreteHerglotzSpectralAmount_pos :
    ratLt ratZero concreteHerglotzSpectralAmount := by
  unfold concreteHerglotzSpectralAmount
  exact BEDC.Derived.RHRoute.HerglotzKernelPositivity.concrete_zero_contribution_pos.right

theorem dvp_budget_nonneg (A B C : Rat)
    (hA : ratLe ratZero A) (hB : ratLe ratZero B) (hC : ratLe ratZero C) :
    ratLe ratZero (dvpBudget A B C) := by
  unfold dvpBudget
  have firstNonneg :
      ratLe ratZero (ratMul (natRat 3) A) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg (natRat_nonneg_local 3) hA
  have secondNonneg :
      ratLe ratZero (ratMul (natRat 4) B) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg (natRat_nonneg_local 4) hB
  exact ratAdd_nonneg_local
    (ratAdd_nonneg_local firstNonneg secondNonneg) hC

theorem dvp_budget_ge_weighted_first (A B C : Rat)
    (hB : ratLe ratZero B) (hC : ratLe ratZero C) :
    ratLe (ratMul (natRat 3) A) (dvpBudget A B C) := by
  unfold dvpBudget
  have secondNonneg :
      ratLe ratZero (ratMul (natRat 4) B) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg (natRat_nonneg_local 4) hB
  exact ratLe_trans
    (ratLe_add_nonneg_right_local
      (ratMul (natRat 3) A) (ratMul (natRat 4) B) secondNonneg)
    (ratLe_add_nonneg_right_local
      (ratAdd (ratMul (natRat 3) A) (ratMul (natRat 4) B)) C hC)

theorem dvp_trig_weight_nonneg (c : Rat) :
    ratLe ratZero
      (BEDC.Derived.RHRoute.ThreeFourOneSOS.threeFourOneCosForm c) := by
  exact BEDC.Derived.RHRoute.ThreeFourOneSOS.cos_form_nonneg c

theorem dvp_shadow_absurd (A B C : Rat)
    (hA : ratLe ratZero A) (hB : ratLe ratZero B) (hC : ratLe ratZero C)
    (hshadow : ratLt (dvpBudget A B C) ratZero) :
    False := by
  exact ratLt_not_ratLe_reverse hshadow
    (dvp_budget_nonneg A B C hA hB hC)

theorem budget_exceeded_absurd (lower budget B : Rat)
    (hcert : ratLe lower budget)
    (hbud : ratLe budget B)
    (hviol : ratLt B lower) :
    False := by
  exact ratLt_not_ratLe_reverse hviol (ratLe_trans hcert hbud)

theorem concrete_dvp_budget_pos :
    ratLt ratZero (dvpBudget concreteHerglotzSpectralAmount ratZero ratZero) := by
  unfold dvpBudget
  have firstPos :
      ratLt ratZero (ratMul (natRat 3) concreteHerglotzSpectralAmount) :=
    ratMul_pos_local (natRat_pos_local (n := 3) (Nat.succ_pos 2))
      concreteHerglotzSpectralAmount_pos
  have secondNonneg :
      ratLe ratZero (ratMul (natRat 4) ratZero) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg
      (natRat_nonneg_local 4) (ratLe_refl ratZero)
  exact ratAdd_pos_of_pos_nonneg_local
    (ratAdd_pos_of_pos_nonneg_local firstPos secondNonneg)
    (ratLe_refl ratZero)

end BEDC.Derived.RHRoute.ExclusionCertifiedBudget
