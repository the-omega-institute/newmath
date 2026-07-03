import BEDC.Derived.RHRoute.PassiveFiniteScattering
import BEDC.Algebra.Rel.Basic
import BEDC.Derived.RationalOrderArithUp

/-
R0-v1 — genuine n-dimensional finite passive scattering (the OCLSD lane's resonance re-aim,
oracle conv_a81113b61ea4f112 turn 3, "action-first" design).

The scalar foundation (`PassiveFiniteScattering`, R0 v0) proved the 1-D passivity
`noUpperHalfPlaneResonancePair : Im z ≤ 0`.  This module builds the TRUE n-dimensional passivity:
`H_eff = A - i B B^*` with `A` self-adjoint, whose resonances all sit in the closed lower
half-plane.  The design is **action-first** — never materialise a general `matMul` or the product
`Γ = B B^*`; define `B^† v` directly as an adjoint ACTION and `B B^† v := BAct (BAdjAct v)`.  Then
passivity needs only ONE load-bearing n-dimensional identity, `⟨v, B w⟩ = ⟨B^† v, w⟩`, after which
the Gram PSD gate and the energy identity are one-line calc's.

Vectors/matrices are plain **`List`** (`CVec = List BComplex`, `CMat = List CVec`) so every
elimination goes through `List.rec` — propext-free (an indexed `Vec : Nat → Type` leaks `propext`
under the equation compiler).  `cinner` truncates to the shorter list and `vAdd` PADS with the
longer tail, which makes the bilinearity lemmas hold for ALL lists (no length hypothesis).  The
`BComplex` scalar layer (arithmetic + `conj_mul_self_re/im` + `cNormSq_nonneg`) is reused from R0 v0.
0-axiom / propext-free.  `SpectralZeroIdentity` untouched (resonance/absorption side, NON-overlapping
with the Weil-PSD lane).
-/

namespace BEDC.Derived.RHRoute.PassiveFiniteScatteringMatrix

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.PassiveFiniteScattering
open BEDC.Derived.RHRoute.PassiveFiniteScattering.BComplex

set_option maxHeartbeats 400000

/-- Finite located-complex vector. -/
abbrev CVec := List BComplex

/-- **Linear** row·vector dot `Σ_j x_j y_j` (NO conjugation), truncated to the shorter list — the
true matrix row action, deliberately distinct from the sesquilinear `cinner`. -/
def rowDot : CVec → CVec → BComplex
  | [], _ => cZero
  | _, [] => cZero
  | x :: xs, y :: ys => cAdd (cMul x y) (rowDot xs ys)

/-- Entrywise conjugation. -/
def conjVec : CVec → CVec
  | [] => []
  | x :: xs => cConj x :: conjVec xs

/-- Sesquilinear inner product `⟨u,v⟩ = Σ conj(u_i) v_i`, truncated to the shorter list. -/
def cinner : CVec → CVec → BComplex
  | [], _ => cZero
  | _, [] => cZero
  | u :: us, v :: vs => cAdd (cMul (cConj u) v) (cinner us vs)

/-- Squared norm `Σ |v_i|²`. -/
def vNormSq : CVec → RatNum
  | [] => ratZero
  | x :: xs => ratAdd (cNormSq x) (vNormSq xs)

/-- Vector addition, PADDING with the longer tail (so `vAdd [] y = y`).  This makes `cinner`
additivity hold for lists of any lengths. -/
def vAdd : CVec → CVec → CVec
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => cAdd x y :: vAdd xs ys

/-- Scalar multiplication of a vector. -/
def cSmulVec (a : BComplex) : CVec → CVec
  | [] => []
  | x :: xs => cMul a x :: cSmulVec a xs

/-- The squared norm is nonnegative (term-by-term located PSD gate). -/
theorem vNormSq_nonneg : (v : CVec) → ratLe ratZero (vNormSq v)
  | [] => ratLe_refl ratZero
  | x :: xs => ratAdd_nonneg (cNormSq_nonneg x) (vNormSq_nonneg xs)

/-- **Vector Gram diagonal, real part**: `⟨v,v⟩.re = ‖v‖²`. -/
theorem cinner_self_re : (v : CVec) → RatEq (cinner v v).re (vNormSq v)
  | [] => RatEq_refl _
  | x :: xs => ratAdd_respects (conj_mul_self_re x) (cinner_self_re xs)

/-- **Vector Gram diagonal, imaginary part**: `⟨v,v⟩.im = 0`. -/
theorem cinner_self_im : (v : CVec) → RatEq (cinner v v).im ratZero
  | [] => RatEq_refl _
  | x :: xs =>
      RatEq_trans _ _ _
        (ratAdd_respects (conj_mul_self_im x) (cinner_self_im xs))
        (ratZero_add_left ratZero)

/-! ## BComplex ring layer (container-independent, propext-free). -/

private theorem ratMul_zero_left_local (x : RatNum) :
    RatEq (ratMul ratZero x) ratZero :=
  BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_left x

private theorem ratMul_zero_right_local (x : RatNum) :
    RatEq (ratMul x ratZero) ratZero :=
  BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_right x

/-- Located equality of complex scalars. -/
def CEq (x y : BComplex) : Prop :=
  RatEq x.re y.re ∧ RatEq x.im y.im

theorem CEq_refl (x : BComplex) : CEq x x :=
  ⟨RatEq_refl x.re, RatEq_refl x.im⟩

theorem CEq_symm {x y : BComplex} : CEq x y -> CEq y x
  | ⟨hre, him⟩ => ⟨RatEq_symm hre, RatEq_symm him⟩

theorem CEq_trans {x y z : BComplex} : CEq x y -> CEq y z -> CEq x z
  | ⟨hxyre, hxyim⟩, ⟨hyzre, hyzim⟩ =>
      ⟨RatEq_trans _ _ _ hxyre hyzre, RatEq_trans _ _ _ hxyim hyzim⟩

def cOfRat (r : RatNum) : BComplex :=
  ⟨r, ratZero⟩

theorem cAdd_respects {x x' y y' : BComplex} :
    CEq x x' -> CEq y y' -> CEq (cAdd x y) (cAdd x' y')
  | ⟨xre, xim⟩, ⟨yre, yim⟩ =>
      ⟨ratAdd_respects xre yre, ratAdd_respects xim yim⟩

theorem cConj_respects {x y : BComplex} :
    CEq x y -> CEq (cConj x) (cConj y)
  | ⟨hre, him⟩ =>
      ⟨hre, BEDC.Derived.RationalUp.ratNeg_respects him⟩

theorem cMul_respects {x x' y y' : BComplex} :
    CEq x x' -> CEq y y' -> CEq (cMul x y) (cMul x' y')
  | ⟨xre, xim⟩, ⟨yre, yim⟩ =>
      ⟨ratAdd_respects (ratMul_respects xre yre)
          (BEDC.Derived.RationalUp.ratNeg_respects (ratMul_respects xim yim)),
        ratAdd_respects (ratMul_respects xre yim) (ratMul_respects xim yre)⟩

theorem cAdd_comm (x y : BComplex) :
    CEq (cAdd x y) (cAdd y x) :=
  ⟨ratAdd_comm x.re y.re, ratAdd_comm x.im y.im⟩

theorem cAdd_assoc (x y z : BComplex) :
    CEq (cAdd (cAdd x y) z) (cAdd x (cAdd y z)) :=
  ⟨BEDC.Derived.LocatedReal.ratAdd_assoc_local x.re y.re z.re,
    BEDC.Derived.LocatedReal.ratAdd_assoc_local x.im y.im z.im⟩

theorem cAdd_zero_left (x : BComplex) :
    CEq (cAdd cZero x) x :=
  ⟨ratZero_add_left x.re, ratZero_add_left x.im⟩

theorem cAdd_zero_right (x : BComplex) :
    CEq (cAdd x cZero) x :=
  ⟨ratAdd_zero_right x.re, ratAdd_zero_right x.im⟩

private theorem ratSub_respects_local {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (BEDC.Derived.RationalUp.ratNeg_respects hy)

private theorem ratMul_neg_right_local (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact BEDC.Derived.RationalUp.IntEq_refl _

private theorem ratMul_neg_left_local (x y : RatNum) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) :=
  RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right_local y x)
      (BEDC.Derived.RationalUp.ratNeg_respects (ratMul_comm y x)))

private theorem ratMul_neg_neg_local (x y : RatNum) :
    RatEq (ratMul (ratNeg x) (ratNeg y)) (ratMul x y) :=
  RatEq_trans _ _ _
    (ratMul_neg_left_local x (ratNeg y))
    (RatEq_trans _ _ _
      (BEDC.Derived.RationalUp.ratNeg_respects (ratMul_neg_right_local x y))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul x y)))

private theorem ratAdd_four_swap_local (a b c d : RatNum) :
    RatEq (ratAdd (ratAdd a b) (ratAdd c d))
      (ratAdd (ratAdd a c) (ratAdd b d)) := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local a b (ratAdd c d))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl a)
        (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local b c d)))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl a)
          (ratAdd_respects (ratAdd_comm b c) (RatEq_refl d)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl a)
            (BEDC.Derived.LocatedReal.ratAdd_assoc_local c b d))
          (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local a c (ratAdd b d))))))

private theorem ratMul_sub_left_local (a b c : RatNum) :
    RatEq (ratMul a (ratSub b c)) (ratSub (ratMul a b) (ratMul a c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left a b (ratNeg c))
    (ratAdd_respects (RatEq_refl (ratMul a b)) (ratMul_neg_right_local a c))

private theorem ratMul_sub_right_local (a b c : RatNum) :
    RatEq (ratMul (ratSub a b) c) (ratSub (ratMul a c) (ratMul b c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_right a (ratNeg b) c)
    (ratAdd_respects (RatEq_refl (ratMul a c)) (ratMul_neg_left_local b c))

theorem cMul_comm (x y : BComplex) :
    CEq (cMul x y) (cMul y x) := by
  unfold cMul
  exact
    ⟨RatEq_trans _ _ _
        (ratSub_respects_local (ratMul_comm x.re y.re) (ratMul_comm x.im y.im))
        (RatEq_refl _),
      RatEq_trans _ _ _
        (ratAdd_respects (ratMul_comm x.re y.im) (ratMul_comm x.im y.re))
        (ratAdd_comm (ratMul y.im x.re) (ratMul y.re x.im))⟩

theorem cMul_add_left (x y z : BComplex) :
    CEq (cMul x (cAdd y z)) (cAdd (cMul x y) (cMul x z)) := by
  unfold cMul cAdd
  constructor
  · have leftExpanded :
        RatEq
          (ratSub (ratMul x.re (ratAdd y.re z.re))
            (ratMul x.im (ratAdd y.im z.im)))
          (ratSub
            (ratAdd (ratMul x.re y.re) (ratMul x.re z.re))
            (ratAdd (ratMul x.im y.im) (ratMul x.im z.im))) :=
      ratSub_respects_local
        (BEDC.Real.RatNumKernel.ratMul_add_left x.re y.re z.re)
        (BEDC.Real.RatNumKernel.ratMul_add_left x.im y.im z.im)
    have regroup :
        RatEq
          (ratSub
            (ratAdd (ratMul x.re y.re) (ratMul x.re z.re))
            (ratAdd (ratMul x.im y.im) (ratMul x.im z.im)))
          (ratAdd
            (ratSub (ratMul x.re y.re) (ratMul x.im y.im))
            (ratSub (ratMul x.re z.re) (ratMul x.im z.im))) := by
      unfold ratSub
      exact RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl _)
          (BEDC.Derived.LocatedReal.ratNeg_add_dist_local
            (ratMul x.im y.im) (ratMul x.im z.im)))
        (ratAdd_four_swap_local _ _ _ _)
    exact RatEq_trans _ _ _ leftExpanded regroup
  · exact RatEq_trans _ _ _
      (ratAdd_respects
        (BEDC.Real.RatNumKernel.ratMul_add_left x.re y.im z.im)
        (BEDC.Real.RatNumKernel.ratMul_add_left x.im y.re z.re))
      (RatEq_symm (ratAdd_four_swap_local _ _ _ _))

theorem cMul_add_right (x y z : BComplex) :
    CEq (cMul (cAdd x y) z) (cAdd (cMul x z) (cMul y z)) := by
  exact CEq_trans (cMul_comm (cAdd x y) z)
    (CEq_trans (cMul_add_left z x y)
      (cAdd_respects (cMul_comm z x) (cMul_comm z y)))

/-- Reorder the four located products of the complex-multiply real part:
`(P−Q)−(R+S) ≈ (P−R)−(S+Q)`. -/
private theorem ratReassoc_re (P Q R S : RatNum) :
    RatEq (ratSub (ratSub P Q) (ratAdd R S)) (ratSub (ratSub P R) (ratAdd S Q)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl _) (BEDC.Derived.LocatedReal.ratNeg_add_dist_local R S))
    (RatEq_trans _ _ _
      (RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local P (ratNeg Q) (ratAdd (ratNeg R) (ratNeg S)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl P)
            (RatEq_trans _ _ _
              (ratAdd_comm (ratNeg Q) (ratAdd (ratNeg R) (ratNeg S)))
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local (ratNeg R) (ratNeg S) (ratNeg Q))))
          (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local P (ratNeg R)
            (ratAdd (ratNeg S) (ratNeg Q))))))
      (ratAdd_respects (RatEq_refl _)
        (RatEq_symm (BEDC.Derived.LocatedReal.ratNeg_add_dist_local S Q))))

/-- Reorder the four located products of the complex-multiply imaginary part:
`(a+b)+(c+d) ≈ (a+c)+(d+b)`. -/
private theorem ratReassoc_im (a b c d : RatNum) :
    RatEq (ratAdd (ratAdd a b) (ratAdd c d)) (ratAdd (ratAdd a c) (ratAdd d b)) :=
  RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local a b (ratAdd c d))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl a)
        (RatEq_trans _ _ _
          (ratAdd_comm b (ratAdd c d))
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local c d b)))
      (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local a c (ratAdd d b))))

theorem cMul_assoc (x y z : BComplex) :
    CEq (cMul (cMul x y) z) (cMul x (cMul y z)) := by
  constructor
  · unfold cMul
    change RatEq
      (ratSub
        (ratMul (ratSub (ratMul x.re y.re) (ratMul x.im y.im)) z.re)
        (ratMul (ratAdd (ratMul x.re y.im) (ratMul x.im y.re)) z.im))
      (ratSub
        (ratMul x.re (ratSub (ratMul y.re z.re) (ratMul y.im z.im)))
        (ratMul x.im (ratAdd (ratMul y.re z.im) (ratMul y.im z.re))))
    have leftExpand :
        RatEq
          (ratSub
            (ratMul (ratSub (ratMul x.re y.re) (ratMul x.im y.im)) z.re)
            (ratMul (ratAdd (ratMul x.re y.im) (ratMul x.im y.re)) z.im))
          (ratSub
            (ratSub (ratMul (ratMul x.re y.re) z.re)
              (ratMul (ratMul x.im y.im) z.re))
            (ratAdd (ratMul (ratMul x.re y.im) z.im)
              (ratMul (ratMul x.im y.re) z.im))) :=
      ratSub_respects_local
        (ratMul_sub_right_local (ratMul x.re y.re) (ratMul x.im y.im) z.re)
        (BEDC.Real.RatNumKernel.ratMul_add_right
          (ratMul x.re y.im) (ratMul x.im y.re) z.im)
    have rightExpand :
        RatEq
          (ratSub
            (ratMul x.re (ratSub (ratMul y.re z.re) (ratMul y.im z.im)))
            (ratMul x.im (ratAdd (ratMul y.re z.im) (ratMul y.im z.re))))
          (ratSub
            (ratSub (ratMul x.re (ratMul y.re z.re))
              (ratMul x.re (ratMul y.im z.im)))
            (ratAdd (ratMul x.im (ratMul y.re z.im))
              (ratMul x.im (ratMul y.im z.re)))) :=
      ratSub_respects_local
        (ratMul_sub_left_local x.re (ratMul y.re z.re) (ratMul y.im z.im))
        (BEDC.Real.RatNumKernel.ratMul_add_left
          x.im (ratMul y.re z.im) (ratMul y.im z.re))
    have term11 :
        RatEq (ratMul (ratMul x.re y.re) z.re)
          (ratMul x.re (ratMul y.re z.re)) :=
      ratMul_assoc x.re y.re z.re
    have term22 :
        RatEq (ratMul (ratMul x.im y.im) z.re)
          (ratMul x.im (ratMul y.im z.re)) :=
      ratMul_assoc x.im y.im z.re
    have term12 :
        RatEq (ratMul (ratMul x.re y.im) z.im)
          (ratMul x.re (ratMul y.im z.im)) :=
      ratMul_assoc x.re y.im z.im
    have term21 :
        RatEq (ratMul (ratMul x.im y.re) z.im)
          (ratMul x.im (ratMul y.re z.im)) :=
      ratMul_assoc x.im y.re z.im
    exact RatEq_trans _ _ _ leftExpand
      (RatEq_trans _ _ _
        (ratSub_respects_local
          (ratSub_respects_local term11 term22)
          (ratAdd_respects term12 term21))
        (RatEq_trans _ _ _
          (ratReassoc_re (ratMul x.re (ratMul y.re z.re)) (ratMul x.im (ratMul y.im z.re))
            (ratMul x.re (ratMul y.im z.im)) (ratMul x.im (ratMul y.re z.im)))
          (RatEq_symm rightExpand)))
  · unfold cMul
    change RatEq
      (ratAdd
        (ratMul (ratSub (ratMul x.re y.re) (ratMul x.im y.im)) z.im)
        (ratMul (ratAdd (ratMul x.re y.im) (ratMul x.im y.re)) z.re))
      (ratAdd
        (ratMul x.re (ratAdd (ratMul y.re z.im) (ratMul y.im z.re)))
        (ratMul x.im (ratSub (ratMul y.re z.re) (ratMul y.im z.im))))
    have leftExpand :
        RatEq
          (ratAdd
            (ratMul (ratSub (ratMul x.re y.re) (ratMul x.im y.im)) z.im)
            (ratMul (ratAdd (ratMul x.re y.im) (ratMul x.im y.re)) z.re))
          (ratAdd
            (ratSub (ratMul (ratMul x.re y.re) z.im)
              (ratMul (ratMul x.im y.im) z.im))
            (ratAdd (ratMul (ratMul x.re y.im) z.re)
              (ratMul (ratMul x.im y.re) z.re))) :=
      ratAdd_respects
        (ratMul_sub_right_local (ratMul x.re y.re) (ratMul x.im y.im) z.im)
        (BEDC.Real.RatNumKernel.ratMul_add_right
          (ratMul x.re y.im) (ratMul x.im y.re) z.re)
    have rightExpand :
        RatEq
          (ratAdd
            (ratMul x.re (ratAdd (ratMul y.re z.im) (ratMul y.im z.re)))
            (ratMul x.im (ratSub (ratMul y.re z.re) (ratMul y.im z.im))))
          (ratAdd
            (ratAdd (ratMul x.re (ratMul y.re z.im))
              (ratMul x.re (ratMul y.im z.re)))
            (ratSub (ratMul x.im (ratMul y.re z.re))
              (ratMul x.im (ratMul y.im z.im)))) :=
      ratAdd_respects
        (BEDC.Real.RatNumKernel.ratMul_add_left
          x.re (ratMul y.re z.im) (ratMul y.im z.re))
        (ratMul_sub_left_local x.im (ratMul y.re z.re) (ratMul y.im z.im))
    have termA :
        RatEq (ratMul (ratMul x.re y.re) z.im)
          (ratMul x.re (ratMul y.re z.im)) :=
      ratMul_assoc x.re y.re z.im
    have termB :
        RatEq (ratMul (ratMul x.im y.im) z.im)
          (ratMul x.im (ratMul y.im z.im)) :=
      ratMul_assoc x.im y.im z.im
    have termC :
        RatEq (ratMul (ratMul x.re y.im) z.re)
          (ratMul x.re (ratMul y.im z.re)) :=
      ratMul_assoc x.re y.im z.re
    have termD :
        RatEq (ratMul (ratMul x.im y.re) z.re)
          (ratMul x.im (ratMul y.re z.re)) :=
      ratMul_assoc x.im y.re z.re
    unfold ratSub at leftExpand rightExpand
    exact RatEq_trans _ _ _ leftExpand
      (RatEq_trans _ _ _
        (ratAdd_respects
          (ratAdd_respects termA
            (BEDC.Derived.RationalUp.ratNeg_respects termB))
          (ratAdd_respects termC termD))
        (RatEq_trans _ _ _
          (ratReassoc_im (ratMul x.re (ratMul y.re z.im))
            (ratNeg (ratMul x.im (ratMul y.im z.im)))
            (ratMul x.re (ratMul y.im z.re)) (ratMul x.im (ratMul y.re z.re)))
          (RatEq_symm rightExpand)))

theorem cConj_add (x y : BComplex) :
    CEq (cConj (cAdd x y)) (cAdd (cConj x) (cConj y)) :=
  ⟨RatEq_refl _,
    BEDC.Derived.LocatedReal.ratNeg_add_dist_local x.im y.im⟩

theorem cConj_mul (x y : BComplex) :
    CEq (cConj (cMul x y)) (cMul (cConj x) (cConj y)) := by
  unfold cConj cMul
  constructor
  · exact ratSub_respects_local (RatEq_refl _) (RatEq_symm (ratMul_neg_neg_local x.im y.im))
  · exact RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratNeg_add_dist_local (ratMul x.re y.im) (ratMul x.im y.re))
      (ratAdd_respects
        (RatEq_symm (ratMul_neg_right_local x.re y.im))
        (RatEq_symm (ratMul_neg_left_local x.im y.re)))

theorem cConj_conj (x : BComplex) :
    CEq (cConj (cConj x)) x :=
  ⟨RatEq_refl x.re, BEDC.Derived.LocatedReal.ratNeg_neg_local x.im⟩

/-- `0·x = 0` at complex level. -/
theorem cMul_zero_left (x : BComplex) : CEq (cMul cZero x) cZero :=
  ⟨RatEq_trans _ _ _
      (ratSub_respects_local (ratMul_zero_left_local x.re) (ratMul_zero_left_local x.im))
      (BEDC.Derived.LocatedReal.ratAdd_neg_local ratZero),
    RatEq_trans _ _ _
      (ratAdd_respects (ratMul_zero_left_local x.im) (ratMul_zero_left_local x.re))
      (ratZero_add_left ratZero)⟩

/-- `x·0 = 0` at complex level. -/
theorem cMul_zero_right (x : BComplex) : CEq (cMul x cZero) cZero :=
  CEq_trans (cMul_comm x cZero) (cMul_zero_left x)

/-- `-i`. -/
def cNegI : BComplex := ⟨ratZero, ratNeg ratOne⟩

/-- `.im` of a complex sum (defining projection; used as a rewrite rule after the operations are
made opaque below). -/
theorem cAdd_im_eq (x y : BComplex) : (cAdd x y).im = ratAdd x.im y.im := rfl

/-- `Im(z · r) = (Im z)·r` for a real scalar `r`. -/
theorem im_mul_ofRat (z : BComplex) (r : RatNum) :
    RatEq (cMul z (cOfRat r)).im (ratMul z.im r) := by
  show RatEq (ratAdd (ratMul z.re ratZero) (ratMul z.im r)) (ratMul z.im r)
  exact RatEq_trans _ _ _
    (ratAdd_respects (ratMul_zero_right_local z.re) (RatEq_refl _))
    (ratZero_add_left (ratMul z.im r))

/-- `Im((-i) · r) = -r` for a real scalar `r`. -/
theorem im_negI_mul_ofRat (r : RatNum) :
    RatEq (cMul cNegI (cOfRat r)).im (ratNeg r) := by
  show RatEq (ratAdd (ratMul ratZero ratZero) (ratMul (ratNeg ratOne) r)) (ratNeg r)
  exact RatEq_trans _ _ _
    (ratAdd_respects (ratMul_zero_left_local ratZero)
      (RatEq_trans _ _ _ (ratMul_neg_left_local ratOne r)
        (BEDC.Derived.RationalUp.ratNeg_respects (ratOne_mul_left r))))
    (ratZero_add_left (ratNeg r))

/- From here on treat the located-complex operations as opaque symbols satisfying the ring lemmas
above: `isDefEq` compares `cAdd`/`cMul`/`cConj` expressions structurally instead of unfolding them
into the located-rational `num`/`den` internals (which blows up `whnf`).  Every ring lemma that
needs to unfold them is already proven above. -/
attribute [local irreducible]
  BEDC.Derived.RHRoute.PassiveFiniteScattering.BComplex.cAdd
  BEDC.Derived.RHRoute.PassiveFiniteScattering.BComplex.cMul
  BEDC.Derived.RHRoute.PassiveFiniteScattering.BComplex.cConj

/-! ## Vector bilinearity (List term-mode, propext-free; `cinner` truncates + `vAdd` pads so these
hold for lists of any lengths). -/

theorem cinner_self_eq_normSq (v : CVec) :
    CEq (cinner v v) (cOfRat (vNormSq v)) :=
  ⟨cinner_self_re v, cinner_self_im v⟩

/-- `cinner` is additive in its FIRST argument. -/
theorem cinner_add_left : (x y z : CVec) →
    CEq (cinner (vAdd x y) z) (cAdd (cinner x z) (cinner y z))
  | [], y, z => CEq_symm (cAdd_zero_left (cinner y z))
  | a :: xs, [], z => CEq_symm (cAdd_zero_right (cinner (a :: xs) z))
  | _ :: _, _ :: _, [] => CEq_symm (cAdd_zero_left cZero)
  | a :: xs, b :: ys, c :: zs =>
      have tail := cinner_add_left xs ys zs
      have headL : CEq (cMul (cConj (cAdd a b)) c)
          (cAdd (cMul (cConj a) c) (cMul (cConj b) c)) :=
        CEq_trans (cMul_respects (cConj_add a b) (CEq_refl c))
          (cMul_add_right (cConj a) (cConj b) c)
      have swap : CEq
          (cAdd (cAdd (cMul (cConj a) c) (cMul (cConj b) c))
            (cAdd (cinner xs zs) (cinner ys zs)))
          (cAdd (cAdd (cMul (cConj a) c) (cinner xs zs))
            (cAdd (cMul (cConj b) c) (cinner ys zs))) :=
        CEq_trans
          (cAdd_assoc (cMul (cConj a) c) (cMul (cConj b) c)
            (cAdd (cinner xs zs) (cinner ys zs)))
          (CEq_trans
            (cAdd_respects (CEq_refl (cMul (cConj a) c))
              (CEq_symm (cAdd_assoc (cMul (cConj b) c) (cinner xs zs) (cinner ys zs))))
            (CEq_trans
              (cAdd_respects (CEq_refl (cMul (cConj a) c))
                (cAdd_respects (cAdd_comm (cMul (cConj b) c) (cinner xs zs))
                  (CEq_refl (cinner ys zs))))
              (CEq_trans
                (cAdd_respects (CEq_refl (cMul (cConj a) c))
                  (cAdd_assoc (cinner xs zs) (cMul (cConj b) c) (cinner ys zs)))
                (CEq_symm (cAdd_assoc (cMul (cConj a) c) (cinner xs zs)
                  (cAdd (cMul (cConj b) c) (cinner ys zs)))))))
      CEq_trans (cAdd_respects headL tail) swap

/-- `cinner` is additive in its SECOND argument. -/
theorem cinner_add_right : (u x y : CVec) →
    CEq (cinner u (vAdd x y)) (cAdd (cinner u x) (cinner u y))
  | [], x, y => CEq_symm (cAdd_zero_left cZero)
  | u :: us, [], y => CEq_symm (cAdd_zero_left (cinner (u :: us) y))
  | u :: us, a :: xs, [] => CEq_symm (cAdd_zero_right (cinner (u :: us) (a :: xs)))
  | u :: us, a :: xs, b :: ys =>
      have tail := cinner_add_right us xs ys
      have headR : CEq (cMul (cConj u) (cAdd a b))
          (cAdd (cMul (cConj u) a) (cMul (cConj u) b)) :=
        cMul_add_left (cConj u) a b
      have swap : CEq
          (cAdd (cAdd (cMul (cConj u) a) (cMul (cConj u) b))
            (cAdd (cinner us xs) (cinner us ys)))
          (cAdd (cAdd (cMul (cConj u) a) (cinner us xs))
            (cAdd (cMul (cConj u) b) (cinner us ys))) :=
        CEq_trans
          (cAdd_assoc (cMul (cConj u) a) (cMul (cConj u) b)
            (cAdd (cinner us xs) (cinner us ys)))
          (CEq_trans
            (cAdd_respects (CEq_refl (cMul (cConj u) a))
              (CEq_symm (cAdd_assoc (cMul (cConj u) b) (cinner us xs) (cinner us ys))))
            (CEq_trans
              (cAdd_respects (CEq_refl (cMul (cConj u) a))
                (cAdd_respects (cAdd_comm (cMul (cConj u) b) (cinner us xs))
                  (CEq_refl (cinner us ys))))
              (CEq_trans
                (cAdd_respects (CEq_refl (cMul (cConj u) a))
                  (cAdd_assoc (cinner us xs) (cMul (cConj u) b) (cinner us ys)))
                (CEq_symm (cAdd_assoc (cMul (cConj u) a) (cinner us xs)
                  (cAdd (cMul (cConj u) b) (cinner us ys)))))))
      CEq_trans (cAdd_respects headR tail) swap

/-- Pulling a scalar out of the second argument: `⟨u, a•v⟩ = a·⟨u,v⟩`. -/
theorem cinner_smul_right : (u v : CVec) → (a : BComplex) →
    CEq (cinner u (cSmulVec a v)) (cMul a (cinner u v))
  | [], v, a => CEq_symm (cMul_zero_right a)
  | u :: us, [], a => CEq_symm (cMul_zero_right a)
  | u :: us, v :: vs, a =>
      have tail := cinner_smul_right us vs a
      CEq_trans
        (cAdd_respects
          (CEq_trans (CEq_symm (cMul_assoc (cConj u) a v))
            (CEq_trans (cMul_respects (cMul_comm (cConj u) a) (CEq_refl v))
              (cMul_assoc a (cConj u) v)))
          tail)
        (CEq_symm (cMul_add_left a (cMul (cConj u) v) (cinner us vs)))

/-! ## Matrix action layer (List `CMat`; action-first, no materialised `matMul`). -/

/-- Finite located-complex row-major matrix. -/
abbrev CMat := List CVec

/-- Linear matrix action `(B w)_i = rowDot (row_i) w`. -/
def BAct : CMat → CVec → CVec
  | [], _ => []
  | row :: rows, w => rowDot row w :: BAct rows w

/-- Scale-and-conjugate a row by `x`: the `α`-th entry is `conj(B_{iα})·x`. -/
def rowAdjScale (x : BComplex) : CVec → CVec
  | [] => []
  | b :: bs => cMul (cConj b) x :: rowAdjScale x bs

/-- Adjoint action `(B† v)_α = Σ_i conj(B_{iα}) v_i`, built as an action (no transpose matrix). -/
def BAdjAct : CMat → CVec → CVec
  | [], _ => []
  | _ :: _, [] => []
  | row :: rows, x :: xs => vAdd (rowAdjScale x row) (BAdjAct rows xs)

/-- `⟨rowAdjScale x row, w⟩ = conj(x)·rowDot row w`. -/
theorem cinner_rowAdjScale : (x : BComplex) → (row w : CVec) →
    CEq (cinner (rowAdjScale x row) w) (cMul (cConj x) (rowDot row w))
  | x, [], _ => CEq_symm (cMul_zero_right (cConj x))
  | x, _ :: _, [] => CEq_symm (cMul_zero_right (cConj x))
  | x, b :: bs, w :: ws =>
      have tail := cinner_rowAdjScale x bs ws
      have head : CEq (cMul (cConj (cMul (cConj b) x)) w) (cMul (cConj x) (cMul b w)) :=
        CEq_trans
          (cMul_respects (cConj_mul (cConj b) x) (CEq_refl w))
          (CEq_trans
            (cMul_respects (cMul_respects (cConj_conj b) (CEq_refl (cConj x))) (CEq_refl w))
            (CEq_trans
              (cMul_respects (cMul_comm b (cConj x)) (CEq_refl w))
              (cMul_assoc (cConj x) b w)))
      CEq_trans
        (cAdd_respects head tail)
        (CEq_symm (cMul_add_left (cConj x) (cMul b w) (rowDot bs ws)))

/-- `⟨v, []⟩ = 0` (needed because `cinner`'s first arm stalls on a variable left argument). -/
theorem cinner_nil_right : (v : CVec) → cinner v [] = cZero
  | [] => rfl
  | _ :: _ => rfl

/-- **The load-bearing adjoint identity**: `⟨v, B w⟩ = ⟨B† v, w⟩`.  Single row recursion — no
matrix-multiply associativity, no Fubini sum-interchange. -/
theorem BAct_adjoint : (B : CMat) → (v w : CVec) →
    CEq (cinner v (BAct B w)) (cinner (BAdjAct B v) w)
  | [], v, _ => by
      show CEq (cinner v []) cZero
      rw [cinner_nil_right v]
      exact CEq_refl cZero
  | _ :: _, [], _ => CEq_refl cZero
  | row :: rows, x :: xs, w =>
      have ih := BAct_adjoint rows xs w
      CEq_trans
        (cAdd_respects (CEq_refl (cMul (cConj x) (rowDot row w))) ih)
        (CEq_trans
          (cAdd_respects (CEq_symm (cinner_rowAdjScale x row w))
            (CEq_refl (cinner (BAdjAct rows xs) w)))
          (CEq_symm (cinner_add_left (rowAdjScale x row) (BAdjAct rows xs) w)))

/-- The Gram action `B B† v` (never materialised as a matrix product). -/
def GramAct (B : CMat) (v : CVec) : CVec :=
  BAct B (BAdjAct B v)

/-- **Gram PSD identity**: `⟨v, B B† v⟩ = ‖B† v‖²` (a real, nonnegative located rational). -/
theorem gram_quad_eq_normSq (B : CMat) (v : CVec) :
    CEq (cinner v (GramAct B v)) (cOfRat (vNormSq (BAdjAct B v))) :=
  CEq_trans (BAct_adjoint B v (BAdjAct B v)) (cinner_self_eq_normSq (BAdjAct B v))

theorem gram_quad_re_nonneg (B : CMat) (v : CVec) :
    ratLe ratZero (cinner v (GramAct B v)).re :=
  BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    (vNormSq_nonneg (BAdjAct B v)) (RatEq_symm (gram_quad_eq_normSq B v).1)

theorem gram_quad_im_zero (B : CMat) (v : CVec) :
    RatEq (cinner v (GramAct B v)).im ratZero :=
  (gram_quad_eq_normSq B v).2

/-! ## Located vector equality (propext-free `def`, NOT an indexed inductive) + inner congruence. -/

/-- Pointwise located equality of vectors (structural `def`, so elimination is propext-free). -/
def VecRatEq : CVec → CVec → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | x :: xs, y :: ys => CEq x y ∧ VecRatEq xs ys

/-- `cinner` is a congruence in its second argument along `VecRatEq`. -/
theorem cinner_congr_right : (v y y' : CVec) → VecRatEq y y' → CEq (cinner v y) (cinner v y')
  | [], _, _, _ => CEq_refl cZero
  | _ :: _, [], [], _ => CEq_refl cZero
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim
  | u :: us, b :: ys, c :: y's, h =>
      cAdd_respects (cMul_respects (CEq_refl (cConj u)) h.1)
        (cinner_congr_right us ys y's h.2)

/-! ## R0-v1.5 — self-adjoint contract, effective Hamiltonian, resonance, and passivity. -/

/-- **Self-adjoint action contract** (oracle's `RealQuadraticAction`): `A` acts with a real diagonal
quadratic form `⟨v, A v⟩ ∈ ℝ` — exactly what `A = A^*` delivers.  Positing it directly is the honest
carrier (like v0's `ScalarPassiveKit` positing `gamma ≥ 0`), sidestepping the char≠2 halving. -/
def RealDiagonalAction (A : CMat) : Prop :=
  ∀ v : CVec, RatEq (cinner v (BAct A v)).im ratZero

theorem selfAdjoint_quad_im_zero (A : CMat) (hA : RealDiagonalAction A) (v : CVec) :
    RatEq (cinner v (BAct A v)).im ratZero :=
  hA v

/-- Nonzero certificate: a positive located lower bound on `‖v‖²` (positive information). -/
structure NonZeroCert (v : CVec) : Type where
  pos_norm : ratLt ratZero (vNormSq v)

/-- Effective (non-self-adjoint) action `H_eff v = A v - i (B B† v)`: Hermitian `A` plus a PSD leak
`Γ = B B†`.  Built entirely from actions — no materialised `matMul`. -/
def HeffAct (A B : CMat) (v : CVec) : CVec :=
  vAdd (BAct A v) (cSmulVec cNegI (GramAct B v))

/-- A resonance pair: a nonzero `v` with `H_eff v = z • v` (kernel-pair certificate, no determinant). -/
structure ResPair (A B : CMat) (z : BComplex) : Type where
  v : CVec
  nz : NonZeroCert v
  eig : VecRatEq (HeffAct A B v) (cSmulVec z v)

/-- **Passive energy identity**: `(Im z)·‖v‖² + ‖B† v‖² = 0`.  Take `⟨v, ·⟩` of the resonance
equation; the Hermitian part gives a real diagonal, the leak gives `-i‖B†v‖²`, the right side gives
`(Im z)‖v‖²`.  Consumes the Gram PSD identity. -/
theorem passive_energy_identity (A B : CMat) (z : BComplex)
    (hA : RealDiagonalAction A) (v : CVec)
    (eig : VecRatEq (HeffAct A B v) (cSmulVec z v)) :
    RatEq (ratAdd (ratMul z.im (vNormSq v)) (vNormSq (BAdjAct B v))) ratZero := by
  have lhs : CEq (cinner v (HeffAct A B v))
      (cAdd (cinner v (BAct A v)) (cMul cNegI (cOfRat (vNormSq (BAdjAct B v))))) :=
    CEq_trans (cinner_add_right v (BAct A v) (cSmulVec cNegI (GramAct B v)))
      (cAdd_respects (CEq_refl (cinner v (BAct A v)))
        (CEq_trans (cinner_smul_right v (GramAct B v) cNegI)
          (cMul_respects (CEq_refl cNegI) (gram_quad_eq_normSq B v))))
  have rhs : CEq (cinner v (cSmulVec z v)) (cMul z (cOfRat (vNormSq v))) :=
    CEq_trans (cinner_smul_right v v z)
      (cMul_respects (CEq_refl z) (cinner_self_eq_normSq v))
  have keyIm : RatEq (cinner v (HeffAct A B v)).im (cinner v (cSmulVec z v)).im :=
    (cinner_congr_right v (HeffAct A B v) (cSmulVec z v) eig).2
  have lhsIm : RatEq (cinner v (HeffAct A B v)).im (ratNeg (vNormSq (BAdjAct B v))) := by
    refine RatEq_trans _ _ _ lhs.2 ?_
    rw [cAdd_im_eq]
    exact RatEq_trans _ _ _
      (ratAdd_respects (hA v) (im_negI_mul_ofRat (vNormSq (BAdjAct B v))))
      (ratZero_add_left (ratNeg (vNormSq (BAdjAct B v))))
  have rhsIm : RatEq (cinner v (cSmulVec z v)).im (ratMul z.im (vNormSq v)) :=
    RatEq_trans _ _ _ rhs.2 (im_mul_ofRat z (vNormSq v))
  have combined : RatEq (ratMul z.im (vNormSq v)) (ratNeg (vNormSq (BAdjAct B v))) :=
    RatEq_trans _ _ _ (RatEq_symm rhsIm) (RatEq_trans _ _ _ (RatEq_symm keyIm) lhsIm)
  exact RatEq_trans _ _ _
    (ratAdd_respects combined (RatEq_refl (vNormSq (BAdjAct B v))))
    (BEDC.Derived.LocatedReal.ratNeg_add_local (vNormSq (BAdjAct B v)))

/-- A located negative of a nonnegative rational is `≤ 0`. -/
private theorem ratNeg_nonpos_local {x : RatNum} (h : ratLe ratZero x) :
    ratLe (ratNeg x) ratZero := by
  have hEq : RatEq x (ratSub ratZero (ratNeg x)) :=
    RatEq_symm (RatEq_trans _ _ _
      (ratZero_add_left (ratNeg (ratNeg x)))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local x))
  exact BEDC.Derived.RHRoute.OCLSDReflectionForm.ratLe_of_sub_nonneg (ratNeg x) ratZero
    (ratLe_of_RatEq_right h hEq)

/-- **No upper-half-plane resonance** (Thm 20.5 resonance side, n-D): a passive finite open system
`H_eff = A - i B B†` (`A` self-adjoint) has every resonance in the closed lower half-plane,
`Im z ≤ 0`.  From `(Im z)‖v‖² = -‖B†v‖² ≤ 0` and `‖v‖² > 0`, cancelling the positive `‖v‖²`.  No
eigenvalue theory, determinant, or square root — pure finite located-complex linear algebra.
0-axiom / propext-free; `SpectralZeroIdentity` untouched. -/
theorem noUpperHalfPlaneResonancePair (A B : CMat) (z : BComplex)
    (hA : RealDiagonalAction A) (rp : ResPair A B z) :
    ratLe z.im ratZero := by
  have energy := passive_energy_identity A B z hA rp.v rp.eig
  have hEq : RatEq (ratMul z.im (vNormSq rp.v)) (ratNeg (vNormSq (BAdjAct B rp.v))) := by
    refine RatEq_trans _ _ _
      (RatEq_symm (ratAdd_zero_right (ratMul z.im (vNormSq rp.v)))) ?_
    refine RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl _)
        (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_neg_local (vNormSq (BAdjAct B rp.v))))) ?_
    refine RatEq_trans _ _ _
      (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local
        (ratMul z.im (vNormSq rp.v)) (vNormSq (BAdjAct B rp.v))
        (ratNeg (vNormSq (BAdjAct B rp.v))))) ?_
    exact RatEq_trans _ _ _
      (ratAdd_respects energy (RatEq_refl _))
      (ratZero_add_left (ratNeg (vNormSq (BAdjAct B rp.v))))
  have hle : ratLe (ratMul z.im (vNormSq rp.v)) ratZero :=
    ratLe_of_RatEq_left hEq
      (ratNeg_nonpos_local (vNormSq_nonneg (BAdjAct B rp.v)))
  have hle2 : ratLe (ratMul z.im (vNormSq rp.v)) (ratMul ratZero (vNormSq rp.v)) :=
    ratLe_of_RatEq_right hle (RatEq_symm (ratMul_zero_left_local (vNormSq rp.v)))
  exact ratMul_le_cancel_right rp.nz.pos_norm hle2

end BEDC.Derived.RHRoute.PassiveFiniteScatteringMatrix
