import BEDC.Real.RatNumKernel
import BEDC.Real.RatNumLogEnclosure
import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Derived.RHRoute.OCLSDReflectionForm
import BEDC.Derived.RHRoute.LocatedGenerationTower

/-
Finite passive open-system (scattering) semantics — the OCLSD lane's re-aim after S1
(oracle conv_a81113b61ea4f112).

S1 (Weyl-counting gate) disproved SpectralZeroIdentity for the BC-locked generator
`H_OCLSD = log n`: its spectrum is `{log n}` (lattice / smooth-number Weyl law), categorically
≠ the zeros' `T log T` Riemann–von Mangoldt count.  The correct re-aim (paper Thm 20.5: zeros are
scattering *resonances*, not a self-adjoint point spectrum) is a **finite passive open system**:
an effective (non-self-adjoint) Hamiltonian `H_eff = A - (i/2) B B^*` with `A` Hermitian, whose
resonances all sit in the closed lower half-plane by passivity.  This is `NON-overlapping` with
the shared RH lane's Weil-form PSD brick — it is the resonance/absorption side.

This module is the scalar foundation: located-complex arithmetic `BComplex = LocatedComplex RatNum`
and the norm-square `cNormSq = re² + im²`, whose nonnegativity is the SAME located-PSD /
complete-the-square fact used by the reflection-positivity brick (`OCLSDReflectionForm.ratSq_nonneg`).
0-axiom / propext-free.
-/

namespace BEDC.Derived.RHRoute.PassiveFiniteScattering

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.OCLSDReflectionForm
open BEDC.Derived.RHRoute.LocatedGenerationTower

/-- Located-complex scalar: a pair of located rationals `(re, im)`. -/
abbrev BComplex := LocatedComplex RatNum

namespace BComplex

/-- `0 : BComplex`. -/
def cZero : BComplex := ⟨ratZero, ratZero⟩

/-- `1 : BComplex`. -/
def cOne : BComplex := ⟨ratOne, ratZero⟩

/-- The imaginary unit `i`. -/
def cI : BComplex := ⟨ratZero, ratOne⟩

/-- Complex addition. -/
def cAdd (x y : BComplex) : BComplex := ⟨ratAdd x.re y.re, ratAdd x.im y.im⟩

/-- Complex negation. -/
def cNeg (x : BComplex) : BComplex := ⟨ratNeg x.re, ratNeg x.im⟩

/-- Complex subtraction. -/
def cSub (x y : BComplex) : BComplex := ⟨ratSub x.re y.re, ratSub x.im y.im⟩

/-- Complex multiplication `(a+bi)(c+di) = (ac-bd) + (ad+bc)i`. -/
def cMul (x y : BComplex) : BComplex :=
  ⟨ratSub (ratMul x.re y.re) (ratMul x.im y.im),
   ratAdd (ratMul x.re y.im) (ratMul x.im y.re)⟩

/-- Complex conjugation `(a+bi)^* = a - bi`. -/
def cConj (x : BComplex) : BComplex := ⟨x.re, ratNeg x.im⟩

/-- Scalar imaginary part (a located rational). -/
def cIm (x : BComplex) : RatNum := x.im

/-- Scalar real part (a located rational). -/
def cRe (x : BComplex) : RatNum := x.re

/-- Norm square `|a+bi|² = a² + b²`, a located rational. -/
def cNormSq (x : BComplex) : RatNum := ratAdd (ratSq x.re) (ratSq x.im)

/-- Sum of two nonnegative located rationals is nonnegative (public reusable form; the same
fact is `private` in `OCLSDReflectionForm`). -/
theorem ratAdd_nonneg {a b : RatNum} (ha : ratLe ratZero a) (hb : ratLe ratZero b) :
    ratLe ratZero (ratAdd a b) :=
  ratLe_of_RatEq_left (RatEq_symm (ratZero_add_left ratZero)) (ratAdd_le_add ha hb)

/-- **The scalar PSD gate**: `0 ≤ |z|²`.  This is exactly the located-square-nonnegativity /
complete-the-square fact behind the reflection-positivity brick — the resonance brick and the
reflection-positivity brick share the same underlying PSD checker. -/
theorem cNormSq_nonneg (x : BComplex) : ratLe ratZero (cNormSq x) :=
  ratAdd_nonneg (ratSq_nonneg x.re) (ratSq_nonneg x.im)

/-- Local zero recognizer for located rationals. -/
private theorem ratNum_zero_to_RatEq_zero_local {x : RatNum} :
    BEDC.Derived.RationalUp.IntEq x.num BEDC.Derived.RationalUp.intZero ->
      RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt ratZero))
      (BEDC.Derived.RationalUp.IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt ratZero))
        BEDC.Derived.RationalUp.intZero :=
    BEDC.Derived.RationalUp.IntEq_trans
      (BEDC.Derived.RationalUp.intMul_left_congr (c := x.num) ratDenInt_zero)
      (BEDC.Derived.RationalUp.IntEq_trans
        (BEDC.Derived.RationalUp.intMul_one_right x.num) numZero)
  have rightToZero :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul ratZero.num (ratDenInt x))
        BEDC.Derived.RationalUp.intZero := by
    change
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero (ratDenInt x))
        BEDC.Derived.RationalUp.intZero
    exact BEDC.Derived.RationalUp.intMul_zero_left (ratDenInt x)
  exact BEDC.Derived.RationalUp.IntEq_trans leftToZero
    (BEDC.Derived.RationalUp.IntEq_symm rightToZero)

/-- `0*x = 0` for located rationals. -/
private theorem ratMul_zero_left_local (x : RatNum) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero_local
  unfold ratMul ratZero intToRat
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero x.num)
      BEDC.Derived.RationalUp.intZero
  exact BEDC.Derived.RationalUp.intMul_zero_left x.num

/-- `x*0 = 0` for located rationals. -/
private theorem ratMul_zero_right_local (x : RatNum) :
    RatEq (ratMul x ratZero) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm x ratZero) (ratMul_zero_left_local x)

/-- Denominators are unchanged by located negation. -/
private theorem ratDenInt_neg_local (x : RatNum) :
    BEDC.Derived.RationalUp.IntEq (ratDenInt (ratNeg x)) (ratDenInt x) := by
  unfold ratDenInt ratNeg
  exact BEDC.Derived.RationalUp.IntEq_refl
    (BEDC.Derived.RationalUp.intOfNat x.den (ratDenCarrier x))

/-- `x*(-y) = -(x*y)` for located rationals. -/
private theorem ratMul_neg_right_local (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · exact BEDC.Derived.RationalUp.IntEq_trans (ratDenInt_mul x (ratNeg y))
      (BEDC.Derived.RationalUp.IntEq_trans
        (BEDC.Derived.RationalUp.IntMul_respects
          (BEDC.Derived.RationalUp.IntEq_refl (ratDenInt x))
          (ratDenInt_neg_local y))
        (BEDC.Derived.RationalUp.IntEq_trans
          (BEDC.Derived.RationalUp.IntEq_symm (ratDenInt_mul x y))
          (BEDC.Derived.RationalUp.IntEq_symm (ratDenInt_neg_local (ratMul x y)))))

/-- `(-x)*y = -(x*y)` for located rationals. -/
private theorem ratMul_neg_left_local (x y : RatNum) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · exact BEDC.Algebra.Rel.IntegerUp_neg_mul x.num y.num
  · exact BEDC.Derived.RationalUp.IntEq_trans (ratDenInt_mul (ratNeg x) y)
      (BEDC.Derived.RationalUp.IntEq_trans
        (BEDC.Derived.RationalUp.IntMul_respects
          (ratDenInt_neg_local x)
          (BEDC.Derived.RationalUp.IntEq_refl (ratDenInt y)))
        (BEDC.Derived.RationalUp.IntEq_trans
          (BEDC.Derived.RationalUp.IntEq_symm (ratDenInt_mul x y))
          (BEDC.Derived.RationalUp.IntEq_symm (ratDenInt_neg_local (ratMul x y)))))

/-- Double negation for located rationals. -/
private theorem ratNeg_neg_local (x : RatNum) :
    RatEq (ratNeg (ratNeg x)) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_neg x.num
  · exact BEDC.Derived.RationalUp.IntEq_trans (ratDenInt_neg_local (ratNeg x))
      (ratDenInt_neg_local x)

/-- `x + (-x) = 0` for located rationals. -/
private theorem ratAdd_neg_local (x : RatNum) :
    RatEq (ratAdd x (ratNeg x)) ratZero := by
  apply ratNum_zero_to_RatEq_zero_local
  unfold ratAdd ratNeg
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt (ratNeg x)))
        (BEDC.Derived.RationalUp.IntMul
          (BEDC.Derived.RationalUp.IntNeg x.num) (ratDenInt x)))
      BEDC.Derived.RationalUp.intZero
  have leftDen :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt (ratNeg x)))
        (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt x)) :=
    BEDC.Derived.RationalUp.IntMul_respects
      (BEDC.Derived.RationalUp.IntEq_refl x.num) (ratDenInt_neg_local x)
  have rightNeg :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul
          (BEDC.Derived.RationalUp.IntNeg x.num) (ratDenInt x))
        (BEDC.Derived.RationalUp.IntNeg
          (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt x))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt x)
  exact BEDC.Derived.RationalUp.IntEq_trans
    (BEDC.Derived.RationalUp.IntAdd_respects leftDen rightNeg)
    (BEDC.Derived.RationalUp.IntAdd_neg
      (BEDC.Derived.RationalUp.IntMul x.num (ratDenInt x)))

/-- `(-x) + x = 0` for located rationals. -/
private theorem ratNeg_add_local (x : RatNum) :
    RatEq (ratAdd (ratNeg x) x) ratZero :=
  RatEq_trans _ _ _ (ratAdd_comm (ratNeg x) x) (ratAdd_neg_local x)

/-- Subtracting a negative is addition. -/
private theorem ratSub_neg_right_local (x y : RatNum) :
    RatEq (ratSub x (ratNeg y)) (ratAdd x y) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl x) (ratNeg_neg_local y))
    (RatEq_refl (ratAdd x y))

/-- The real part of `conj x * x` is `|x|²`. -/
theorem conj_mul_self_re (x : BComplex) :
    RatEq (cMul (cConj x) x).re (cNormSq x) := by
  unfold cMul cConj cNormSq ratSq ratSub
  exact ratAdd_respects (RatEq_refl (ratMul x.re x.re))
    (RatEq_trans _ _ _
      (BEDC.Derived.RationalUp.ratNeg_respects (ratMul_neg_left_local x.im x.im))
      (ratNeg_neg_local (ratMul x.im x.im)))

/-- The imaginary part of `conj x * x` is zero. -/
theorem conj_mul_self_im (x : BComplex) :
    RatEq (cMul (cConj x) x).im ratZero := by
  unfold cMul cConj
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl (ratMul x.re x.im))
      (RatEq_trans _ _ _
        (ratMul_neg_left_local x.im x.re)
        (BEDC.Derived.RationalUp.ratNeg_respects (ratMul_comm x.im x.re))))
    (ratAdd_neg_local (ratMul x.re x.im))

end BComplex

/-- Finite vector over located-complex scalars. -/
abbrev CVec := List BComplex

/-- Finite row-major matrix over located-complex scalars. -/
abbrev CMat := List (List BComplex)

/-- Structure-recursive squared norm, with no membership reasoning. -/
def vNormSq : CVec -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd (BComplex.cNormSq x) (vNormSq xs)

/-- Finite vector norm is nonnegative. -/
theorem vNormSq_nonneg (v : CVec) : ratLe ratZero (vNormSq v) := by
  induction v with
  | nil =>
      exact ratLe_refl ratZero
  | cons x xs ih =>
      exact BComplex.ratAdd_nonneg (BComplex.cNormSq_nonneg x) ih

/-- Located-complex addition at scalar level. -/
private def cAdd := BComplex.cAdd

/-- Located-complex multiplication at scalar level. -/
private def cMul := BComplex.cMul

/-- Located-complex conjugation at scalar level. -/
private def cConj := BComplex.cConj

/-- Complex inner product, truncated to the shorter list. -/
def cinner : CVec -> CVec -> BComplex
  | [], _ => BComplex.cZero
  | _, [] => BComplex.cZero
  | u :: us, v :: vs => cAdd (cMul (cConj u) v) (cinner us vs)

/-- Row-major matrix-vector multiplication by structural recursion. -/
def matVec : CMat -> CVec -> CVec
  | [], _ => []
  | row :: rows, v => cinner row v :: matVec rows v

/-- Scalar multiplication of a vector. -/
def cSmul (z : BComplex) : CVec -> CVec
  | [] => []
  | x :: xs => cMul z x :: cSmul z xs

/-- Located equality of complex scalars. -/
def CEq (x y : BComplex) : Prop :=
  RatEq x.re y.re ∧ RatEq x.im y.im

/-- Located equality of vectors, truncated only by exact shape. -/
def VecRatEq : CVec -> CVec -> Prop
  | [], [] => True
  | x :: xs, y :: ys => CEq x y ∧ VecRatEq xs ys
  | [], _ :: _ => False
  | _ :: _, [] => False

/-
**n 维完整 passivity 留作 v1（honest obligation, NOT faked）.**  The real finite passive open
system `H_eff = A - (i/2) B B^*` (A Hermitian, B rational matrices) needs the vector Gram identity
`⟨v, B B^* v⟩ = ‖B^* v‖²` — a genuine located complex inner-product computation with a real
`matMul` / `dagger`.  This v0 does NOT construct it, and deliberately avoids the dishonest
identity placeholder (`matMul M N := M`) that would fake `Γ = B B^*`.  The vector layer above
(`CVec` / `vNormSq` / `cinner` / `matVec` / `cSmul`) is the real scaffolding it will build on.
What v0 proves below is the genuine **one-dimensional concrete instance** of the passivity
semantics. -/

/-- One-dimensional passive scattering data: `a` is real and `gamma` is a nonnegative
located-rational damping strength.  This is the concrete finite instance of the open-system
resonance semantics. -/
structure ScalarPassiveKit where
  a : RatNum
  gamma : RatNum
  gamma_nonneg : ratLe ratZero gamma

/-- The scalar effective Hamiltonian is `a - i gamma`, hence its resonance has imaginary
part `-gamma`. -/
def scalarHeff (K : ScalarPassiveKit) : BComplex :=
  ⟨K.a, ratNeg K.gamma⟩

/-- In one dimension the resonance equation is simply located equality with `a-i gamma`. -/
def ScalarResPair (K : ScalarPassiveKit) (z : BComplex) : Prop :=
  CEq z (scalarHeff K)

/-- Concrete scalar damping quadratic form is nonnegative. -/
theorem Dquad_nonneg (K : ScalarPassiveKit) :
    ratLe ratZero K.gamma :=
  K.gamma_nonneg

/-- The scalar passive energy identity: `Im z = -gamma`. -/
theorem passive_energy_identity (K : ScalarPassiveKit) (z : BComplex)
    (h : ScalarResPair K z) :
    RatEq (BComplex.cIm z) (ratNeg K.gamma) :=
  h.2

/-- A located negative of a nonnegative rational is bounded above by zero. -/
private theorem ratNeg_nonpos_of_nonneg {x : RatNum} (h : ratLe ratZero x) :
    ratLe (ratNeg x) ratZero := by
  have hsub : ratLe ratZero (ratSub ratZero (ratNeg x)) :=
    ratLe_of_RatEq_right h
      (RatEq_symm (RatEq_trans _ _ _
        (BComplex.ratSub_neg_right_local ratZero x)
        (ratZero_add_left x)))
  exact ratLe_of_sub_nonneg (ratNeg x) ratZero hsub

/-- Concrete finite passive scattering has no upper-half-plane resonance.  This is the true
one-dimensional instance of the general finite passive semantics; the full matrix Gram identity
is represented above as carrier structure, not as a stub theorem. -/
theorem noUpperHalfPlaneResonancePair (K : ScalarPassiveKit) (z : BComplex)
    (h : ScalarResPair K z) :
    ratLe (BComplex.cIm z) ratZero :=
  ratLe_of_RatEq_left (passive_energy_identity K z h)
    (ratNeg_nonpos_of_nonneg (Dquad_nonneg K))

/-! ## R0-v1 (n-dimensional passivity, in progress) — vector Gram lemmas. -/

/-- **Vector Gram diagonal (real part)**: `⟨v,v⟩.re = ‖v‖²`.  Lifts the scalar `conj_mul_self_re`
term-by-term over the located inner product — the first load-bearing lemma of the genuine
n-dimensional passivity (NOT the 1-D special case, NOT an identity stub). -/
theorem cinner_self_re : ∀ v : CVec, RatEq (cinner v v).re (vNormSq v)
  | [] => RatEq_refl _
  | x :: xs => ratAdd_respects (BComplex.conj_mul_self_re x) (cinner_self_re xs)

/-- **Vector Gram diagonal (imaginary part)**: `⟨v,v⟩.im = 0`. -/
theorem cinner_self_im : ∀ v : CVec, RatEq (cinner v v).im ratZero
  | [] => RatEq_refl _
  | x :: xs =>
      RatEq_trans _ _ _
        (ratAdd_respects (BComplex.conj_mul_self_im x) (cinner_self_im xs))
        (ratZero_add_left ratZero)

end BEDC.Derived.RHRoute.PassiveFiniteScattering
