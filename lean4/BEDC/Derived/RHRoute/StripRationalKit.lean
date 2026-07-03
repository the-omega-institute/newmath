import BEDC.Derived.RHRoute.StripExclusionAssembly

set_option maxHeartbeats 2000000

/-!
Shared rational-arithmetic kit for the strip-exclusion discharge bricks.

Everything is stated over the exact-rational carrier `RatNum` with the
`qq num den` constructor (`num/den`). The key point is that all comparisons and
equalities are reduced to **binary-Nat cross products** (`a * d ≤ c * b`,
`a * d = c * b`), which `decide` evaluates efficiently, rather than to
`ratLeBool` — the latter forces reduction of the unary `natRat den` term and
stack-overflows on large denominators. Discharge bricks import this kit and stay
short instead of each rebuilding these helpers privately.
-/

namespace BEDC.Derived.RHRoute.StripRationalKit

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

abbrev natRat (n : Nat) : Rat :=
  BEDC.Derived.RHRoute.StripExclusionAssembly.natRat n

def qq (num den : Nat) (hden : 0 < den := by decide) : Rat :=
  BEDC.Derived.RHRoute.StripExclusionAssembly.q num den hden

theorem natRat_apart0_of_pos {n : Nat} (h : 0 < n) :
    ratApart0 (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos h

theorem natRat_pos_of_pos {n : Nat} (h : 0 < n) :
    ratLt ratZero (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos h

theorem natRat_le_of_nat_le {m n : Nat} (h : m ≤ n) :
    ratLe (natRat m) (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumKernel.ratNat_le_of_nat_le h

theorem natRat_lt_of_nat_lt {m n : Nat} (h : m < n) :
    ratLt (natRat m) (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_lt_of_nat_lt h

theorem natRat_mul (m n : Nat) :
    RatEq (ratMul (natRat m) (natRat n)) (natRat (m * n)) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_mul m n

theorem ratLe_congr {x x' y y' : Rat}
    (hx : RatEq x x') (hy : RatEq y y') (h : ratLe x' y') : ratLe x y :=
  ratLe_of_RatEq_right (ratLe_of_RatEq_left hx h) (RatEq_symm hy)

theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

theorem ratNat_mul_le_of_nat_mul_le {a d2 b d1 : Nat}
    (h : a * d2 ≤ b * d1) :
    ratLe (ratMul (natRat a) (natRat d2))
      (ratMul (natRat b) (natRat d1)) :=
  ratLe_congr (natRat_mul a d2) (natRat_mul b d1) (natRat_le_of_nat_le h)

theorem ratNatMul_pos {d1 d2 : Nat} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ratLt ratZero (ratMul (natRat d1) (natRat d2)) :=
  ratLt_of_RatEq_right (natRat_pos_of_pos (Nat.mul_pos hd1 hd2))
    (RatEq_symm (natRat_mul d1 d2))

theorem ratDivApart_mul_cancel_pair_right {x d e : Rat}
    (hd : ratApart0 d) :
    RatEq (ratMul (ratDivApart x d hd) (ratMul d e)) (ratMul x e) :=
  RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc (ratDivApart x d hd) d e))
    (ratMul_respects_left (ratDivApart_mul_cancel_right hd))

theorem ratDivApart_mul_cancel_pair_cross_right {x d e : Rat}
    (he : ratApart0 e) :
    RatEq (ratMul (ratDivApart x e he) (ratMul d e)) (ratMul x d) :=
  RatEq_trans _ _ _
    (ratMul_respects_right (ratMul_comm d e))
    (ratDivApart_mul_cancel_pair_right (x := x) (d := e) (e := d) he)

theorem ratDivApart_crossLe_rat {A B D1 D2 : Rat}
    (hD1 : ratApart0 D1) (hD2 : ratApart0 D2)
    (hCpos : ratLt ratZero (ratMul D1 D2))
    (hCross : ratLe (ratMul A D2) (ratMul B D1)) :
    ratLe (ratDivApart A D1 hD1) (ratDivApart B D2 hD2) := by
  have hLeftEq :
      RatEq (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2)) (ratMul A D2) :=
    ratDivApart_mul_cancel_pair_right (x := A) (d := D1) (e := D2) hD1
  have hRightEq :
      RatEq (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) (ratMul B D1) :=
    ratDivApart_mul_cancel_pair_cross_right (x := B) (d := D1) (e := D2) hD2
  have hScaled :
      ratLe (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2))
        (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) :=
    ratLe_respects (RatEq_symm hLeftEq) (RatEq_symm hRightEq) hCross
  exact ratMul_le_cancel_right hCpos hScaled

/-- `qq a d1 ≤ qq b d2` iff `a * d2 ≤ b * d1` — decides a binary-Nat product,
never reducing the unary denominator. -/
theorem qq_crossLe {a d1 b d2 : Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (h : a * d2 ≤ b * d1) :
    ratLe (qq a d1 hd1) (qq b d2 hd2) := by
  unfold qq BEDC.Derived.RHRoute.StripExclusionAssembly.q
  exact ratDivApart_crossLe_rat
    (natRat_apart0_of_pos hd1) (natRat_apart0_of_pos hd2)
    (ratNatMul_pos hd1 hd2)
    (ratNat_mul_le_of_nat_mul_le h)

/-- `qq a b = qq c d` iff `a * d = c * b` — decides a binary-Nat product
equality, never reducing the unary denominator (so it survives arbitrarily
large denominators, unlike a `ratLeBool`/`decide` proof). -/
theorem qq_eq_of_cross {a b c d : Nat}
    (hb : 0 < b) (hd : 0 < d) (h : a * d = c * b) :
    RatEq (qq a b hb) (qq c d hd) :=
  ratLe_antisymm
    (qq_crossLe hb hd (Nat.le_of_eq h))
    (qq_crossLe hd hb (Nat.le_of_eq h.symm))

/-- Reciprocal denominator monotonicity for a fixed nonnegative numerator:
`0 ≤ x`, `0 < a ≤ b` implies `x / b ≤ x / a`. -/
theorem ratDivApart_le_same_num_den_mono
    {x a b : Rat}
    (hx : ratLe ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLe a b) :
    ratLe (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    ratDivApart_mul_cancel_right haApart
  have divBNonneg :
      ratLe ratZero (ratDivApart x b hbApart) :=
    ratDivApart_nonneg_of_nonneg_pos hx hb hbApart
  have step :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) :=
    ratMul_le_mul_nonneg_left hab divBNonneg
  have toX :
      ratLe (ratMul (ratDivApart x b hbApart) a) x :=
    ratLe_of_RatEq_right step leftCancel
  have targetMul :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    ratLe_of_RatEq_right toX (RatEq_symm rightCancel)
  exact ratMul_le_cancel_right ha targetMul

theorem natRat_add (m n : Nat) :
    RatEq (ratAdd (natRat m) (natRat n)) (natRat (m + n)) := by
  unfold natRat BEDC.Derived.RHRoute.StripExclusionAssembly.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_add m n

theorem ratDivApart_add_same {A C D : Rat} (hD : ratApart0 D) :
    RatEq (ratAdd (ratDivApart A D hD) (ratDivApart C D hD))
      (ratDivApart (ratAdd A C) D hD) := by
  unfold ratDivApart
  exact RatEq_symm (ratMul_add_right A C (ratInvApart D hD))

/-- Same-denominator addition: `a/m + c/m = (a+c)/m`. Combined with
`qq_eq_of_cross` (to bring two fractions to a common denominator first), this
adds fractions with different denominators over concrete rationals without ever
constructing or reducing a large unary `natRat`. -/
theorem qq_add_same_den {a c m : Nat} (hm : 0 < m) :
    RatEq (ratAdd (qq a m hm) (qq c m hm)) (qq (a + c) m hm) := by
  unfold qq BEDC.Derived.RHRoute.StripExclusionAssembly.q
  have numEq :
      RatEq
        (ratDivApart (ratAdd (natRat a) (natRat c)) (natRat m)
          (natRat_apart0_of_pos hm))
        (ratDivApart (natRat (a + c)) (natRat m)
          (natRat_apart0_of_pos hm)) := by
    unfold ratDivApart
    exact ratMul_respects_left (natRat_add a c)
  exact RatEq_trans _ _ _
    (ratDivApart_add_same (natRat_apart0_of_pos hm)) numEq

end BEDC.Derived.RHRoute.StripRationalKit
