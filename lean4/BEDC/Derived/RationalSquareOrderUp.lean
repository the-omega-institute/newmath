import BEDC.Derived.RationalUp
import BEDC.Derived.BoxStreamSqrt2Up

namespace BEDC.Derived.RationalSquareOrderUp

open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp
open BEDC.Derived.BoxStreamSqrt2Up (ratTwo)

theorem ratLt_not_RatEq {x y : RatNum} :
    ratLt x y -> RatEq x y -> False := by
  intro hlt same
  unfold ratLt intLtUp intLt at hlt
  unfold RatEq at same
  have lenEq := IntPairClassifier_length_eq same
  unfold IntMul ratDenInt at hlt
  rw [lenEq] at hlt
  exact Nat.lt_irrefl _ hlt

theorem ratLt_irrefl (x : RatNum) :
    ratLt x x -> False := by
  intro hlt
  exact ratLt_not_RatEq hlt (RatEq_refl x)

theorem ratLt_asymm {x y : RatNum} :
    ratLt x y -> ratLt y x -> False := by
  intro xy yx
  exact ratLt_not_ratLe_reverse xy (ratLt_to_ratLe yx)

theorem ratLt_trans {x y z : RatNum} :
    ratLt x y -> ratLt y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) (ratLt_to_ratLe yz)
  · intro zx
    have zy : ratLe z y :=
      ratLe_trans zx (ratLt_to_ratLe xy)
    exact ratLt_not_ratLe_reverse yz zy

theorem rat_order_trichotomy (x y : RatNum) :
    ratLt x y ∨ RatEq x y ∨ ratLt y x := by
  cases ratLe_decidable x y with
  | inl xy =>
      cases ratLe_decidable y x with
      | inl yx =>
          exact Or.inr (Or.inl (ratLe_antisymm xy yx))
      | inr notYX =>
          exact Or.inl (ratLe_not_le_to_ratLt xy notYX)
  | inr notXY =>
      have yx : ratLe y x := by
        cases ratLe_total x y with
        | inl xy => exact False.elim (notXY xy)
        | inr yx => exact yx
      exact Or.inr (Or.inr (ratLe_not_le_to_ratLt yx notXY))

theorem rat_sq_trichotomy (q : RatNum) :
    ratLt (ratMul q q) ratTwo ∨
      RatEq (ratMul q q) ratTwo ∨
        ratLt ratTwo (ratMul q q) :=
  rat_order_trichotomy (ratMul q q) ratTwo

theorem rat_sq_strictMono {a b : RatNum} :
    ratLe ratZero a -> ratLt a b ->
      ratLt (ratMul a a) (ratMul b b) := by
  intro aNonneg hlt
  have aLeB : ratLe a b := ratLt_to_ratLe hlt
  have bPositive : ratLt ratZero b :=
    ratLe_lt_trans aNonneg hlt
  have aaLeAB : ratLe (ratMul a a) (ratMul a b) :=
    ratLe_respects (RatEq_refl (ratMul a a)) (ratMul_comm b a)
      (ratMul_le_mul_right aLeB aNonneg)
  have abLtBB : ratLt (ratMul a b) (ratMul b b) :=
    ratMul_lt_mul_right hlt bPositive
  exact ratLe_lt_trans aaLeAB abLtBB

theorem rat_sq_not_eq_two_of_lt {q : RatNum} :
    ratLt (ratMul q q) ratTwo -> RatEq (ratMul q q) ratTwo -> False :=
  ratLt_not_RatEq

theorem rat_sq_not_eq_two_of_gt {q : RatNum} :
    ratLt ratTwo (ratMul q q) -> RatEq (ratMul q q) ratTwo -> False := by
  intro hlt same
  exact ratLt_not_RatEq hlt (RatEq_symm same)

end BEDC.Derived.RationalSquareOrderUp
