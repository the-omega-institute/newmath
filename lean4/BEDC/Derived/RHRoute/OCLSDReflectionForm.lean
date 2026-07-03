import BEDC.Real.RatNumKernel
import BEDC.Real.RatNumLogEnclosure
import BEDC.Derived.LocatedReal.GroundedToleranceKit

/-
Finite reflection-positivity ⟺ PSD, the OCLSD tick-dynamics positivity classification.

Innovation-geometry 定理 8.3 / 命题 8.5: for a 2-state reversible tick input the OS reflection
form is `⟨θf, f⟩ = q(f0+f1)² + (1-2q)(f0²+f1²)` (completed-square form), which is `≥ 0` for the
antisymmetric mode `f=(1,-1)` iff `q ≤ 1/2`.  This is the finite discrete mirror of the OCLSD
Hamiltonian's positivity: reflection-positive tick inputs are exactly the ones with a unitary
OS reconstruction (OCLSDHamiltonian posits self-adjointness / a unitary phase flow; here it is
the derivable rational positivity condition).

Honest boundary: this is a finite 2-state classification, NOT `SpectralZeroIdentity` — the
Hilbert–Pólya wall (Spec(H_OCLSD) = ζ zeros) is untouched.  0-axiom / propext-free.  The route
(minimal public bridges, `(-1)²=1` by concrete cross-mult, no general `square_nonneg`) is from
the oracle conv_ff4ff126afd06e33.
-/

namespace BEDC.Derived.RHRoute.OCLSDReflectionForm

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.IntUp
open BEDC.Derived.LocatedReal (ratAdd_neg_local ratNeg_add_local ratAdd_assoc_local ratNeg_neg_local)

/-- `2` as a located rational. -/
def twoRat : RatNum := ratAdd ratOne ratOne
/-- Square. -/
def ratSq (x : RatNum) : RatNum := ratMul x x
/-- The small eigenvalue `1 - 2q` of the 2-state transition matrix. -/
def oneMinusTwoQ (q : RatNum) : RatNum := ratSub ratOne (ratMul twoRat q)

/-- The OS reflection quadratic form (completed-square / manifestly-PSD form):
`osForm q f0 f1 = q(f0+f1)² + (1-2q)(f0²+f1²)`. -/
def osForm (q f0 f1 : RatNum) : RatNum :=
  ratAdd (ratMul q (ratSq (ratAdd f0 f1)))
    (ratMul (oneMinusTwoQ q) (ratAdd (ratSq f0) (ratSq f1)))

/-! ### Minimal located bridges (the private/missing facts the oracle route needs) -/

private theorem ratNum_zero_to_RatEq_zero {x : RatNum}
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

/-- `0 * x = 0`. -/
theorem ratMul_zero_left (x : RatNum) : RatEq (ratMul ratZero x) ratZero :=
  ratNum_zero_to_RatEq_zero (intMul_zero_left x.num)

/-- `x * 0 = 0`. -/
theorem ratMul_zero_right (x : RatNum) : RatEq (ratMul x ratZero) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm x ratZero) (ratMul_zero_left x)

/-- `1 * 1 = 1`. -/
theorem ratOne_sq : RatEq (ratMul ratOne ratOne) ratOne :=
  ratMul_one_right ratOne

/-- `(-1) * (-1) = 1`, by concrete cross-multiplication (no variable whnf). -/
theorem ratNegOne_sq : RatEq (ratMul (ratNeg ratOne) (ratNeg ratOne)) ratOne := by
  apply ratEq_of_num_den_intEq <;> exact IntEq_refl _

/-- `1 = ratNat 1`. -/
theorem ratOne_eq_ratNat_one : RatEq ratOne (ratNat 1) := by
  apply ratEq_of_num_den_intEq <;> exact IntEq_refl _

/-- `twoRat = ratNat 2`. -/
theorem twoRat_eq_ratNat_two : RatEq twoRat (ratNat 2) := by
  unfold twoRat
  exact RatEq_trans _ _ _
    (ratAdd_respects ratOne_eq_ratNat_one ratOne_eq_ratNat_one) (ratNat_add 1 1)

/-- `0 < 2`. -/
theorem ratZero_lt_twoRat : ratLt ratZero twoRat :=
  ratLt_of_RatEq_right (ratNat_pos_of_pos (Nat.succ_pos 1))
    (RatEq_symm twoRat_eq_ratNat_two)

/-- `0 ≤ 2`. -/
theorem ratZero_le_twoRat : ratLe ratZero twoRat :=
  ratLt_to_ratLe ratZero_lt_twoRat

/-- `ratNat 0 = 0`. -/
theorem ratNat_zero : RatEq (ratNat 0) ratZero := by
  apply ratEq_of_num_den_intEq <;> exact IntEq_refl _

/-- `0 ≤ 1`. -/
theorem ratZero_le_one : ratLe ratZero ratOne :=
  ratLe_of_RatEq_left (RatEq_symm ratNat_zero)
    (ratLe_of_RatEq_right (ratNat_le_of_nat_le (Nat.zero_le 1))
      (RatEq_symm ratOne_eq_ratNat_one))

/-! ### The reduction and the two classification theorems -/

private theorem ratSq_one_plus_negOne :
    RatEq (ratSq (ratAdd ratOne (ratNeg ratOne))) ratZero := by
  show RatEq (ratMul (ratAdd ratOne (ratNeg ratOne)) (ratAdd ratOne (ratNeg ratOne))) ratZero
  have h0 : RatEq (ratAdd ratOne (ratNeg ratOne)) ratZero :=
    BEDC.Derived.LocatedReal.ratAdd_neg_local ratOne
  exact RatEq_trans _ _ _ (ratMul_respects h0 h0) (ratMul_zero_left ratZero)

/-- On the antisymmetric mode `(1,-1)` the OS form collapses to the eigenvalue: `osForm q 1
(-1) = (1-2q)·2` (the first, `q(f0+f1)²`, term vanishes since `1+(-1)=0`). -/
theorem osForm_one_negOne_eq (q : RatNum) :
    RatEq (osForm q ratOne (ratNeg ratOne)) (ratMul (oneMinusTwoQ q) twoRat) := by
  unfold osForm
  have hFirst : RatEq (ratMul q (ratSq (ratAdd ratOne (ratNeg ratOne)))) ratZero :=
    RatEq_trans _ _ _ (ratMul_respects_right ratSq_one_plus_negOne)
      (ratMul_zero_right q)
  have hSecondArg :
      RatEq (ratAdd (ratSq ratOne) (ratSq (ratNeg ratOne))) twoRat :=
    ratAdd_respects ratOne_sq ratNegOne_sq
  have hSecond :
      RatEq (ratMul (oneMinusTwoQ q) (ratAdd (ratSq ratOne) (ratSq (ratNeg ratOne))))
        (ratMul (oneMinusTwoQ q) twoRat) :=
    ratMul_respects_right hSecondArg
  exact RatEq_trans _ _ _ (ratAdd_respects hFirst hSecond)
    (ratZero_add_left (ratMul (oneMinusTwoQ q) twoRat))

/-- **RP holds on the antisymmetric mode** when `2q ≤ 1` (i.e. `q ≤ 1/2`): the reflection form
is `≥ 0` — the reflection-positive / unitary-reconstructable regime. -/
theorem reflection_holds_flip (q : RatNum) (h : ratLe (ratMul twoRat q) ratOne) :
    ratLe ratZero (osForm q ratOne (ratNeg ratOne)) := by
  have hSub : ratLe ratZero (oneMinusTwoQ q) := ratSub_nonneg_of_le h
  have hCore : ratLe ratZero (ratMul (oneMinusTwoQ q) twoRat) :=
    ratMul_nonneg hSub ratZero_le_twoRat
  exact ratLe_of_RatEq_right hCore (RatEq_symm (osForm_one_negOne_eq q))

/-- `(a - b) + b = a`. -/
private theorem ratSub_add_cancel (a b : RatNum) : RatEq (ratAdd (ratSub a b) b) a := by
  show RatEq (ratAdd (ratAdd a (ratNeg b)) b) a
  exact RatEq_trans _ _ _ (ratAdd_assoc_local a (ratNeg b) b)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl a) (ratNeg_add_local b))
      (ratAdd_zero_right a))

/-- `a < b ⟹ a - b < 0` (public strict-subtraction bridge; add `b`/`-b` to both sides and
use `ratLt_not_ratLe_reverse` for strictness — no private neg/order facts). -/
theorem ratSub_lt_zero_of_lt {a b : RatNum} (h : ratLt a b) :
    ratLt (ratSub a b) ratZero := by
  apply ratLe_not_le_to_ratLt
  · have step : ratLe (ratAdd a (ratNeg b)) (ratAdd b (ratNeg b)) :=
      ratAdd_le_add (ratLt_to_ratLe h) (ratLe_refl (ratNeg b))
    exact ratLe_of_RatEq_right step (ratAdd_neg_local b)
  · intro h0
    have step : ratLe (ratAdd ratZero b) (ratAdd (ratSub a b) b) :=
      ratAdd_le_add h0 (ratLe_refl b)
    have hba : ratLe b a :=
      ratLe_respects (ratZero_add_left b) (ratSub_add_cancel a b) step
    exact ratLt_not_ratLe_reverse h hba

/-- `0 ≤ b - a ⟹ a ≤ b` (reusable; converse of `ratSub_nonneg_of_le`). -/
theorem ratLe_of_sub_nonneg (a b : RatNum) (h : ratLe ratZero (ratSub b a)) : ratLe a b :=
  ratLe_respects (ratZero_add_left a) (ratSub_add_cancel b a)
    (ratAdd_le_add h (ratLe_refl a))

/-- `1 < 2q ⟹ (1-2q)·2 < 0`. -/
private theorem oneMinusTwoQ_mul_two_lt_zero (q : RatNum)
    (h : ratLt ratOne (ratMul twoRat q)) :
    ratLt (ratMul (oneMinusTwoQ q) twoRat) ratZero := by
  have hSub : ratLt (oneMinusTwoQ q) ratZero := ratSub_lt_zero_of_lt h
  have hScaled : ratLt (ratMul (oneMinusTwoQ q) twoRat) (ratMul ratZero twoRat) :=
    ratMul_lt_mul_right hSub ratZero_lt_twoRat
  exact ratLt_of_RatEq_right hScaled (ratMul_zero_left twoRat)

/-- **RP fails on the antisymmetric mode** when `1 < 2q` (i.e. `q > 1/2`): the reflection form
is `< 0` — an explicit indefinite counterexample (命题 8.5).  Reflection-anticorrelated tick
inputs have NO unitary/self-adjoint OS reconstruction: the reflection-positivity signature is a
*classification condition* on the OCLSD tick dynamics, not an added postulate. -/
theorem reflection_fails (q : RatNum) (h : ratLt ratOne (ratMul twoRat q)) :
    ratLt (osForm q ratOne (ratNeg ratOne)) ratZero :=
  ratLt_of_RatEq_left (osForm_one_negOne_eq q) (oneMinusTwoQ_mul_two_lt_zero q h)

/-! ### Full ∀f positivity (定理 8.3), via a reusable located `ratSq_nonneg` -/

/-- Public neg-mul (core `ratMul_neg_right_local` is private): `x·(-y) = -(x·y)`. -/
private theorem ratMul_neg_right (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · exact IntEq_refl _

/-- `(-x)·(-x) = x·x`. -/
private theorem ratNeg_mul_neg (x : RatNum) :
    RatEq (ratMul (ratNeg x) (ratNeg x)) (ratMul x x) :=
  RatEq_trans _ _ _ (ratMul_neg_right (ratNeg x) x)
    (RatEq_trans _ _ _
      (ratNeg_respects
        (RatEq_trans _ _ _ (ratMul_comm (ratNeg x) x) (ratMul_neg_right x x)))
      (ratNeg_neg_local (ratMul x x)))

/-- `x ≤ 0 ⟹ 0 ≤ -x`. -/
private theorem ratNeg_nonneg_of_nonpos {x : RatNum} (h : ratLe x ratZero) :
    ratLe ratZero (ratNeg x) :=
  ratLe_of_RatEq_right (ratSub_nonneg_of_le h) (ratZero_add_left (ratNeg x))

/-- **`0 ≤ x²`** (reusable located square-nonnegativity: nonneg branch by `ratMul_nonneg`,
nonpos branch by `(-x)² = x²`). -/
theorem ratSq_nonneg (x : RatNum) : ratLe ratZero (ratSq x) := by
  show ratLe ratZero (ratMul x x)
  rcases ratLe_total ratZero x with h | h
  · exact ratMul_nonneg h h
  · exact ratLe_of_RatEq_right
      (ratMul_nonneg (ratNeg_nonneg_of_nonpos h) (ratNeg_nonneg_of_nonpos h))
      (ratNeg_mul_neg x)

/-- `0 ≤ a ⟹ 0 ≤ b ⟹ 0 ≤ a + b`. -/
private theorem ratAdd_nonneg {a b : RatNum}
    (ha : ratLe ratZero a) (hb : ratLe ratZero b) : ratLe ratZero (ratAdd a b) :=
  ratLe_of_RatEq_left (RatEq_symm (ratZero_add_left ratZero)) (ratAdd_le_add ha hb)

/-- **RP holds for EVERY test vector** when `0 ≤ q` and `2q ≤ 1` (定理 8.3 positive direction):
the completed-square form is a sum of two nonnegative terms, so `osForm q f0 f1 ≥ 0` for all
`f0, f1` — full reflection positivity of the tick input in the unitary-reconstructable regime. -/
theorem reflection_holds (q f0 f1 : RatNum) (hq0 : ratLe ratZero q)
    (hq : ratLe (ratMul twoRat q) ratOne) :
    ratLe ratZero (osForm q f0 f1) :=
  ratAdd_nonneg
    (ratMul_nonneg hq0 (ratSq_nonneg (ratAdd f0 f1)))
    (ratMul_nonneg (ratSub_nonneg_of_le hq)
      (ratAdd_nonneg (ratSq_nonneg f0) (ratSq_nonneg f1)))

end BEDC.Derived.RHRoute.OCLSDReflectionForm
