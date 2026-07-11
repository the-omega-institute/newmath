import BEDC.Derived.RHRoute.IntervalMatrixPSD.KernelApproxCerts

/-
Located `qNat` calculator (loop: archimedean obligation, block 3).

Reusable located-rational arithmetic for folding a concrete polynomial endpoint value
(`evalPoly (coeffs.map ratAbs) (qNat 1 8)`, etc.) into a single `qNat`, so the concrete
`*_abs_bound_zeroPanel` obligations reduce to `qNat_crossLe` (block 1).  The tree works its
error budgets on `RawRatBound` (pure Nat) and only reads back to located form; this file
supplies the missing located side: `ratMul` / same-denominator `ratAdd` of `ratDivApart`
values, lifted to `qNat`.

All generic lemmas are stated over `Rat`/`Nat` variables (never over the big concrete
endpoint terms), so the elaborator only ever sees variables — no whnf blowup (block-1
opaque-boundary discipline).  All proofs 0-axiom / propext-free.
-/

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.IntUp
open BEDC.Derived.RHRoute.IntervalMatrixPSD

/-- A located rational whose numerator is zero equals `ratZero` (cross-multiplication:
`x.num = 0` forces both sides of `RatEq x ratZero` to `intZero`). -/
private theorem ratNum_zero_to_RatEq_zero {x : Rat}
    (numZero : IntEq x.num intZero) : RatEq x ratZero := by
  unfold RatEq
  change IntEq (IntMul x.num (ratDenInt ratZero)) (IntMul ratZero.num (ratDenInt x))
  have leftToZero : IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero : IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

/-- Left annihilation: `ratZero * x = ratZero`. -/
theorem ratMul_zero_left (x : Rat) : RatEq (ratMul ratZero x) ratZero :=
  ratNum_zero_to_RatEq_zero (intMul_zero_left x.num)

/-- The located reciprocal respects `RatEq` on its argument.  `inv x = inv x * (y * inv y)
= inv x * (x * inv y) = (inv x * x) * inv y = inv y`. -/
theorem ratInvApart_respects {x y : Rat}
    (hx : ratApart0 x) (hy : ratApart0 y) (hxy : RatEq x y) :
    RatEq (ratInvApart x hx) (ratInvApart y hy) := by
  have invXx : RatEq (ratMul (ratInvApart x hx) x) ratOne :=
    RatEq_trans _ _ _ (ratMul_comm (ratInvApart x hx) x) (ratInvApart_mul x hx)
  have yInvY : RatEq (ratMul y (ratInvApart y hy)) ratOne :=
    ratInvApart_mul y hy
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_one_right (ratInvApart x hx)))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (ratInvApart x hx)) (RatEq_symm yInvY))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratInvApart x hx))
          (ratMul_respects (RatEq_symm hxy) (RatEq_refl (ratInvApart y hy))))
        (RatEq_trans _ _ _
          (RatEq_symm (ratMul_assoc (ratInvApart x hx) x (ratInvApart y hy)))
          (RatEq_trans _ _ _
            (ratMul_respects invXx (RatEq_refl (ratInvApart y hy)))
            (ratOne_mul_left (ratInvApart y hy))))))

/-- Located division respects `RatEq` on numerator and denominator. -/
theorem ratDivApart_respects {A A' D D' : Rat}
    (hD : ratApart0 D) (hD' : ratApart0 D')
    (hA : RatEq A A') (hDeq : RatEq D D') :
    RatEq (ratDivApart A D hD) (ratDivApart A' D' hD') := by
  unfold ratDivApart
  exact ratMul_respects hA (ratInvApart_respects hD hD' hDeq)

/-- Product of located divisions: `(A/D1)*(C/D2) = (A*C)/(D1*D2)`. -/
theorem ratDivApart_mul {A D1 C D2 : Rat}
    (h1 : ratApart0 D1) (h2 : ratApart0 D2) (h12 : ratApart0 (ratMul D1 D2)) :
    RatEq (ratMul (ratDivApart A D1 h1) (ratDivApart C D2 h2))
      (ratDivApart (ratMul A C) (ratMul D1 D2) h12) := by
  unfold ratDivApart
  have invProduct :
      RatEq (ratInvApart (ratMul D1 D2) h12)
        (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)) :=
    ratInvApart_mul_product h1 h2 h12
  -- regroup (A*invD1)*(C*invD2) = (A*C)*(invD1*invD2)
  have regroup :
      RatEq (ratMul (ratMul A (ratInvApart D1 h1)) (ratMul C (ratInvApart D2 h2)))
        (ratMul (ratMul A C) (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2))) := by
    exact RatEq_trans _ _ _
      (ratMul_assoc A (ratInvApart D1 h1) (ratMul C (ratInvApart D2 h2)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl A)
          (RatEq_trans _ _ _
            (RatEq_symm (ratMul_assoc (ratInvApart D1 h1) C (ratInvApart D2 h2)))
            (RatEq_trans _ _ _
              (ratMul_respects (ratMul_comm (ratInvApart D1 h1) C)
                (RatEq_refl (ratInvApart D2 h2)))
              (ratMul_assoc C (ratInvApart D1 h1) (ratInvApart D2 h2)))))
        (RatEq_symm (ratMul_assoc A C
          (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)))))
  exact RatEq_trans _ _ _ regroup
    (ratMul_respects (RatEq_refl (ratMul A C)) (RatEq_symm invProduct))

/-- Same-denominator sum of located divisions: `(A/D)+(C/D) = (A+C)/D`. -/
theorem ratDivApart_add_same {A C D : Rat} (hD : ratApart0 D) :
    RatEq (ratAdd (ratDivApart A D hD) (ratDivApart C D hD))
      (ratDivApart (ratAdd A C) D hD) := by
  unfold ratDivApart
  exact RatEq_symm (ratMul_add_right A C (ratInvApart D hD))

/-- `qNat n m` (positive `m`) as an explicit located division.  `ratApart0` is a `Prop`, so
the witness is proof-irrelevant and this holds definitionally. -/
theorem qNat_pos_eq {n m : Nat} (hm : 0 < m) :
    RatEq (qNat n m)
      (ratDivApart (ratNat n) (ratNat m) (ratNat_apart0_of_pos hm)) := by
  cases m with
  | zero => exact absurd hm (Nat.lt_irrefl 0)
  | succ m' => exact RatEq_refl _

/-- Located `qNat` product: `qNat a b * qNat c d = qNat (a*c) (b*d)`. -/
theorem qNat_mul {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) :
    RatEq (ratMul (qNat a b) (qNat c d)) (qNat (a * c) (b * d)) := by
  have hbd : 0 < b * d := Nat.mul_pos hb hd
  have h12 : ratApart0 (ratMul (ratNat b) (ratNat d)) :=
    ratMul_apart0 (ratNat_apart0_of_pos hb) (ratNat_apart0_of_pos hd)
  exact RatEq_trans _ _ _
    (ratMul_respects (qNat_pos_eq hb) (qNat_pos_eq hd))
    (RatEq_trans _ _ _
      (ratDivApart_mul (ratNat_apart0_of_pos hb) (ratNat_apart0_of_pos hd) h12)
      (RatEq_trans _ _ _
        (ratDivApart_respects h12 (ratNat_apart0_of_pos hbd)
          (ratNat_mul a c) (ratNat_mul b d))
        (RatEq_symm (qNat_pos_eq hbd))))

/-- Same-denominator located `qNat` sum: `qNat a m + qNat c m = qNat (a+c) m`. -/
theorem qNat_add_same_den {a c m : Nat} (hm : 0 < m) :
    RatEq (ratAdd (qNat a m) (qNat c m)) (qNat (a + c) m) := by
  have hApart : ratApart0 (ratNat m) := ratNat_apart0_of_pos hm
  exact RatEq_trans _ _ _
    (ratAdd_respects (qNat_pos_eq hm) (qNat_pos_eq hm))
    (RatEq_trans _ _ _
      (ratDivApart_add_same hApart)
      (RatEq_trans _ _ _
        (ratDivApart_respects hApart hApart (ratNat_add a c) (RatEq_refl (ratNat m)))
        (RatEq_symm (qNat_pos_eq hm))))

end BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator
