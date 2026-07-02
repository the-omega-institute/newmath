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

end BComplex

end BEDC.Derived.RHRoute.PassiveFiniteScattering
