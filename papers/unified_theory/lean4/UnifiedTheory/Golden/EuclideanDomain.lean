import UnifiedTheory.Golden.CoordinateSystem
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Euclidean division on `ℤ[φ]`

This file equips the concrete golden integer ring `PhiInt` with the Euclidean
function induced by the absolute value of the algebraic norm.
-/

namespace UnifiedTheory
namespace PhiInt

instance instNontrivial : Nontrivial PhiInt :=
  ⟨⟨0, 1, by decide⟩⟩

private theorem toRealPlus_eq_zero_iff (x : PhiInt) :
    toRealPlus x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases hb : x.b = 0
    · have haR : (x.a : ℝ) = 0 := by
        simpa [toRealPlus, hb] using h
      have ha : x.a = 0 := by exact_mod_cast haR
      rw [ext_iff]
      exact ⟨ha, hb⟩
    · have hbR : (x.b : ℝ) ≠ 0 := by exact_mod_cast hb
      have hlin : (x.b : ℝ) * Real.goldenRatio = -(x.a : ℝ) := by
        have hh : (x.a : ℝ) + (x.b : ℝ) * Real.goldenRatio = 0 := by
          simpa [toRealPlus] using h
        linarith
      have hphi : Real.goldenRatio = ((-x.a : ℤ) : ℝ) / (x.b : ℝ) := by
        rw [eq_div_iff hbR]
        rw [mul_comm]
        simpa using hlin
      exact False.elim ((Real.goldenRatio_irrational.ne_rational (-x.a) x.b) hphi)
  · intro h
    simp [h, toRealPlus]

private theorem toRealMul_eq_norm (x : PhiInt) :
    toRealPlus x * toRealMinus x = (x.norm : ℝ) := by
  simp only [toRealPlus, toRealMinus]
  rw [Real.goldenConj]
  ring_nf
  rw [Real.sq_sqrt]
  · simp [norm]
    ring
  · norm_num

theorem norm_conj (x : PhiInt) : (conj x).norm = x.norm := by
  simp [norm, conj]
  ring

theorem norm_eq_zero (x : PhiInt) : x.norm = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hprod : toRealPlus x * toRealMinus x = 0 := by
      rw [toRealMul_eq_norm, h]
      norm_num
    rcases mul_eq_zero.mp hprod with hp | hm
    · exact (toRealPlus_eq_zero_iff x).mp hp
    · have hc : conj x = 0 := by
        exact (toRealPlus_eq_zero_iff (conj x)).mp <| by
          simpa [toRealMinus_eq_toRealPlus_conj] using hm
      have hcc := congrArg conj hc
      simpa using hcc
  · intro h
    simp [h, norm]

theorem norm_ne_zero_iff (x : PhiInt) : x.norm ≠ 0 ↔ x ≠ 0 := by
  simpa [Ne] using not_congr (norm_eq_zero x)

instance instNoZeroDivisors : NoZeroDivisors PhiInt where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    have hnorm : x.norm * y.norm = 0 := by
      rw [← norm_mul, hxy]
      simp [norm]
    rcases Int.eq_zero_or_eq_zero_of_mul_eq_zero hnorm with hx | hy
    · exact Or.inl ((norm_eq_zero x).mp hx)
    · exact Or.inr ((norm_eq_zero y).mp hy)

instance instIsDomain : IsDomain PhiInt :=
  NoZeroDivisors.to_isDomain _

def quotient (x y : PhiInt) : PhiInt :=
  let n := x * conj y
  let D := y.norm
  ⟨round ((n.a : ℚ) / (D : ℚ)), round ((n.b : ℚ) / (D : ℚ))⟩

def remainder (x y : PhiInt) : PhiInt :=
  x - y * quotient x y

theorem quotient_zero (x : PhiInt) : quotient x 0 = 0 := by
  simp [quotient, norm]
  rfl

theorem quotient_mul_add_remainder_eq (x y : PhiInt) :
    y * quotient x y + remainder x y = x := by
  simp [remainder]

theorem norm_mul_natAbs (x y : PhiInt) :
    (x * y).norm.natAbs = x.norm.natAbs * y.norm.natAbs := by
  rw [norm_mul, Int.natAbs_mul]

theorem one_le_norm_natAbs_of_ne_zero {x : PhiInt} (hx : x ≠ 0) :
    1 ≤ x.norm.natAbs := by
  exact Nat.succ_le_iff.mpr ((Int.natAbs_pos).mpr ((norm_ne_zero_iff x).mpr hx))

theorem norm_le_norm_mul_left (x : PhiInt) {y : PhiInt} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [norm_mul_natAbs]
  exact le_mul_of_one_le_right (Nat.zero_le _) (one_le_norm_natAbs_of_ne_zero (x := y) hy)

theorem norm_le_norm_mul_right {x : PhiInt} (hx : x ≠ 0) (y : PhiInt) :
    y.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [norm_mul_natAbs]
  exact le_mul_of_one_le_left (Nat.zero_le _) (one_le_norm_natAbs_of_ne_zero (x := x) hx)

private theorem remainder_norm_identity (x y q : PhiInt) :
    let r := x - y * q
    let n := x * conj y
    let D := y.norm
    let sa := n.a - q.a * D
    let sb := n.b - q.b * D
    r.norm * D = sa ^ 2 + sa * sb - sb ^ 2 := by
  simp only [norm, sub_a, sub_b, mul_a, mul_b, conj_a, conj_b]
  ring

private theorem round_remainder_natAbs_le (z D : ℤ) (hD : D ≠ 0) :
    2 * (z - round ((z : ℚ) / (D : ℚ)) * D).natAbs ≤ D.natAbs := by
  let q : ℤ := round ((z : ℚ) / (D : ℚ))
  let s : ℤ := z - q * D
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hround : |(z : ℚ) / (D : ℚ) - (q : ℚ)| ≤ (1 : ℚ) / 2 := by
    simpa [q] using abs_sub_round ((z : ℚ) / (D : ℚ))
  have hs_eq : (s : ℚ) = ((z : ℚ) / (D : ℚ) - (q : ℚ)) * (D : ℚ) := by
    dsimp [s]
    field_simp [hDq]
    push_cast
    ring
  have habs : |(s : ℚ)| ≤ |(D : ℚ)| / 2 := by
    rw [hs_eq, abs_mul]
    have hmul := mul_le_mul_of_nonneg_right hround (abs_nonneg (D : ℚ))
    nlinarith [abs_nonneg (D : ℚ)]
  have hcast : ((2 * s.natAbs : ℕ) : ℚ) ≤ (D.natAbs : ℚ) := by
    simp
    nlinarith [habs, abs_nonneg (D : ℚ)]
  have hnat : 2 * s.natAbs ≤ D.natAbs := by exact_mod_cast hcast
  simpa [s, q]

private theorem quadNatBound (A B C : ℕ) (hA : 2 * A ≤ C) (hB : 2 * B ≤ C) :
    4 * (A ^ 2 + A * B + B ^ 2) ≤ 3 * C ^ 2 := by
  nlinarith [hA, hB]

private theorem quadForm_natAbs_le (a b : ℤ) :
    (a ^ 2 + a * b - b ^ 2).natAbs ≤
      a.natAbs ^ 2 + a.natAbs * b.natAbs + b.natAbs ^ 2 := by
  have hquad :
      |a ^ 2 + a * b - b ^ 2| ≤
        (a.natAbs : ℤ) ^ 2 + (a.natAbs : ℤ) * (b.natAbs : ℤ) + (b.natAbs : ℤ) ^ 2 := by
    calc
      |a ^ 2 + a * b - b ^ 2| = |a ^ 2 + a * b + (-b ^ 2)| := by ring_nf
      _ ≤ |a ^ 2| + |a * b| + |-b ^ 2| := by
        have h1 := abs_add_le (a ^ 2 + a * b) (-b ^ 2)
        have h2 := abs_add_le (a ^ 2) (a * b)
        linarith
      _ = (a.natAbs : ℤ) ^ 2 + (a.natAbs : ℤ) * (b.natAbs : ℤ) + (b.natAbs : ℤ) ^ 2 := by
        rw [abs_pow, abs_mul, abs_neg, abs_pow]
        simp
  rw [← Int.ofNat_le]
  rw [Int.natCast_natAbs]
  norm_num
  simpa using hquad

private theorem quadForm_scaled_le (a b : ℤ) (C : ℕ)
    (ha : 2 * a.natAbs ≤ C) (hb : 2 * b.natAbs ≤ C) :
    4 * (a ^ 2 + a * b - b ^ 2).natAbs ≤ 3 * C ^ 2 := by
  exact (Nat.mul_le_mul_left 4 (quadForm_natAbs_le a b)).trans
    (quadNatBound a.natAbs b.natAbs C ha hb)

theorem remainder_norm_bound (x : PhiInt) {y : PhiInt} (hy : y ≠ 0) :
    4 * (remainder x y).norm.natAbs ≤ 3 * y.norm.natAbs := by
  let q := quotient x y
  let r := x - y * q
  let n := x * conj y
  let D := y.norm
  let sa := n.a - q.a * D
  let sb := n.b - q.b * D
  have hD : D ≠ 0 := (norm_ne_zero_iff y).mpr hy
  have hDpos : 0 < D.natAbs := (Int.natAbs_pos).mpr hD
  have hqa : q.a = round ((n.a : ℚ) / (D : ℚ)) := by
    simp [q, quotient, n, D]
  have hqb : q.b = round ((n.b : ℚ) / (D : ℚ)) := by
    simp [q, quotient, n, D]
  have hsa : 2 * sa.natAbs ≤ D.natAbs := by
    have h := round_remainder_natAbs_le n.a D hD
    simpa [sa, hqa, mul_comm, mul_left_comm, mul_assoc] using h
  have hsb : 2 * sb.natAbs ≤ D.natAbs := by
    have h := round_remainder_natAbs_le n.b D hD
    simpa [sb, hqb, mul_comm, mul_left_comm, mul_assoc] using h
  have hquad : 4 * (sa ^ 2 + sa * sb - sb ^ 2).natAbs ≤ 3 * D.natAbs ^ 2 :=
    quadForm_scaled_le sa sb D.natAbs hsa hsb
  have hid : r.norm.natAbs * D.natAbs = (sa ^ 2 + sa * sb - sb ^ 2).natAbs := by
    have h := congrArg Int.natAbs (remainder_norm_identity x y q)
    simpa [r, n, D, sa, sb, Int.natAbs_mul] using h
  have hmul : 4 * r.norm.natAbs * D.natAbs ≤ 3 * D.natAbs ^ 2 := by
    calc
      4 * r.norm.natAbs * D.natAbs = 4 * (r.norm.natAbs * D.natAbs) := by
        ring
      _ = 4 * (sa ^ 2 + sa * sb - sb ^ 2).natAbs := by
        rw [hid]
      _ ≤ 3 * D.natAbs ^ 2 := hquad
  have hcancel : 4 * r.norm.natAbs ≤ 3 * D.natAbs := by
    have h' : (4 * r.norm.natAbs) * D.natAbs ≤ (3 * D.natAbs) * D.natAbs := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    exact Nat.le_of_mul_le_mul_right h' hDpos
  simpa [remainder, q, r, D]

private theorem lt_of_four_le_three_mul {A B : ℕ} (hB : 0 < B) (h : 4 * A ≤ 3 * B) :
    A < B := by
  by_contra hnot
  have hge : B ≤ A := Nat.le_of_not_gt hnot
  have h4B : 4 * B ≤ 4 * A := Nat.mul_le_mul_left 4 hge
  have h34 : 3 * B < 4 * B := by nlinarith [hB]
  exact (not_lt_of_ge (h4B.trans h)) h34

theorem remainder_norm_lt (x : PhiInt) {y : PhiInt} (hy : y ≠ 0) :
    (remainder x y).norm.natAbs < y.norm.natAbs := by
  exact lt_of_four_le_three_mul ((Int.natAbs_pos).mpr ((norm_ne_zero_iff y).mpr hy))
    (remainder_norm_bound x hy)

instance : EuclideanDomain PhiInt :=
  { PhiInt.instCommRing,
    PhiInt.instNontrivial with
    quotient := quotient
    quotient_zero := quotient_zero
    remainder := remainder
    quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq
    r := fun x y => x.norm.natAbs < y.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := remainder_norm_lt
    mul_left_not_lt := fun x _ hy => not_lt_of_ge (norm_le_norm_mul_left x hy) }

theorem phiInt_ufd : UniqueFactorizationMonoid PhiInt :=
  inferInstance

end PhiInt
end UnifiedTheory
