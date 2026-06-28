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

private theorem intLt_not_intLe_reverse {x y : RatInt} :
    intLtUp x y -> intLe y x -> False := by
  intro hlt hle
  unfold intLtUp at hlt
  unfold intLe at hle
  have hleLen :=
    (BEDC.Derived.IntUp.pairLe_iff_length_order
      (intToPair_carrier y) (intToPair_carrier x)).mp hle
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hleLen)

theorem ratLt_not_ratLe_reverse {x y : RatNum} :
    ratLt x y -> ratLe y x -> False := by
  intro hlt hle
  unfold ratLt at hlt
  unfold ratLe at hle
  exact intLt_not_intLe_reverse hlt hle

theorem ratLt_asymm {x y : RatNum} :
    ratLt x y -> ratLt y x -> False := by
  intro xy yx
  exact ratLt_not_ratLe_reverse xy (ratLt_to_ratLe yx)

theorem ratLe_not_le_to_ratLt {x y : RatNum} :
    ratLe x y -> (ratLe y x -> False) -> ratLt x y := by
  intro xy notYX
  unfold ratLe intLe at xy
  unfold ratLt intLtUp intLt
  have xCarrier := intToPair_carrier (IntMul x.num (ratDenInt y))
  have yCarrier := intToPair_carrier (IntMul y.num (ratDenInt x))
  have xyLen :
      bwordLength (intToPair (IntMul x.num (ratDenInt y))).1 +
          bwordLength (intToPair (IntMul y.num (ratDenInt x))).2 ≤
        bwordLength (intToPair (IntMul y.num (ratDenInt x))).1 +
          bwordLength (intToPair (IntMul x.num (ratDenInt y))).2 :=
    (pairLe_iff_length_order xCarrier yCarrier).mp xy
  have notYXLen :
      ¬
        bwordLength (intToPair (IntMul y.num (ratDenInt x))).1 +
            bwordLength (intToPair (IntMul x.num (ratDenInt y))).2 ≤
          bwordLength (intToPair (IntMul x.num (ratDenInt y))).1 +
            bwordLength (intToPair (IntMul y.num (ratDenInt x))).2 := by
    intro yxLen
    exact notYX ((pairLe_iff_length_order yCarrier xCarrier).mpr yxLen)
  exact Nat.lt_of_le_of_ne xyLen (fun sameLen => notYXLen (Nat.le_of_eq sameLen.symm))

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

theorem rat_sq_not_eq_two_of_lt {q : RatNum} :
    ratLt (ratMul q q) ratTwo -> RatEq (ratMul q q) ratTwo -> False :=
  ratLt_not_RatEq

theorem rat_sq_not_eq_two_of_gt {q : RatNum} :
    ratLt ratTwo (ratMul q q) -> RatEq (ratMul q q) ratTwo -> False := by
  intro hlt same
  exact ratLt_not_RatEq hlt (RatEq_symm same)

end BEDC.Derived.RationalSquareOrderUp
