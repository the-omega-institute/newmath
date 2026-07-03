import BEDC.Derived.RHRoute.PassiveFiniteScattering

/-
R0-v1 — genuine n-dimensional finite passive scattering (the OCLSD lane's resonance re-aim,
oracle conv_a81113b61ea4f112 turn 3, "action-first" design).

The scalar foundation (`PassiveFiniteScattering`, R0 v0) proved the 1-D passivity
`noUpperHalfPlaneResonancePair : Im z ≤ 0`.  This module builds the TRUE n-dimensional passivity:
`H_eff = A - (i/2) B B^*` with `A` self-adjoint, whose resonances all sit in the closed lower
half-plane.  The design is **action-first** — never materialise a general `matMul` or the product
`Γ = B B^*`; define `B^† v` directly as an adjoint ACTION and `B B^† v := BAct (BAdjAct v)`.  Then
passivity needs only ONE load-bearing n-dimensional identity, `⟨v, B w⟩ = ⟨B^† v, w⟩`, after which
the Gram PSD gate and the energy identity are one-line calc's — no matrix-multiply associativity,
no Fubini sum-interchange, no `List.mem_cons`.

Vectors and matrices are **length-indexed inductives** (`Vec n`, `Mat n m`): the shape lives in the
type, so `BAdjAct` on the empty matrix still knows its column count and no `List.length` Prop is
transported.  The `BComplex` scalar layer (arithmetic + `conj_mul_self_re/im` + `cNormSq_nonneg`) is
reused from R0 v0.  0-axiom / propext-free.  `SpectralZeroIdentity` untouched (this is the
resonance/absorption side, NON-overlapping with the Weil-PSD lane).

This file: R0-v1.1 — vector algebra core (`Vec`, linear `rowDot`, `cinner`, `vNormSq`, the diagonal
Gram lemmas `cinner_self_re/im`).
-/

namespace BEDC.Derived.RHRoute.PassiveFiniteScatteringMatrix

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.PassiveFiniteScattering
open BEDC.Derived.RHRoute.PassiveFiniteScattering.BComplex

/-- Length-indexed vector of located-complex scalars: the length lives in the type, so no
`List.length` certificate is ever transported. -/
inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons : {n : Nat} → BComplex → Vec n → Vec (Nat.succ n)

/-- **Linear** row·vector dot `Σ_j x_j y_j` (NO conjugation) — this is the true matrix row action
`(B w)_i`, deliberately distinct from the sesquilinear `cinner` (oracle's key trap: never use
`cinner row v` as a matrix product; it conjugates the row). -/
def rowDot : {n : Nat} → Vec n → Vec n → BComplex
  | 0, Vec.nil, Vec.nil => cZero
  | Nat.succ _, Vec.cons x xs, Vec.cons y ys => cAdd (cMul x y) (rowDot xs ys)

/-- Entrywise conjugation. -/
def conjVec : {n : Nat} → Vec n → Vec n
  | 0, Vec.nil => Vec.nil
  | Nat.succ _, Vec.cons x xs => Vec.cons (cConj x) (conjVec xs)

/-- Sesquilinear inner product `⟨u,v⟩ = Σ_i conj(u_i) v_i` (conjugate on the FIRST argument). -/
def cinner : {n : Nat} → Vec n → Vec n → BComplex
  | 0, Vec.nil, Vec.nil => cZero
  | Nat.succ _, Vec.cons u us, Vec.cons v vs => cAdd (cMul (cConj u) v) (cinner us vs)

/-- Squared norm `Σ_i |v_i|²`, a located rational. -/
def vNormSq : {n : Nat} → Vec n → RatNum
  | 0, Vec.nil => ratZero
  | Nat.succ _, Vec.cons x xs => ratAdd (cNormSq x) (vNormSq xs)

/-- The squared norm is nonnegative (term-by-term located PSD gate). -/
theorem vNormSq_nonneg : {n : Nat} → (v : Vec n) → ratLe ratZero (vNormSq v)
  | 0, Vec.nil => ratLe_refl ratZero
  | Nat.succ _, Vec.cons x xs => ratAdd_nonneg (cNormSq_nonneg x) (vNormSq_nonneg xs)

/-- **Vector Gram diagonal, real part**: `⟨v,v⟩.re = ‖v‖²`.  Lifts the scalar `conj_mul_self_re`
term-by-term over the located inner product — a genuine n-dimensional lemma. -/
theorem cinner_self_re : {n : Nat} → (v : Vec n) → RatEq (cinner v v).re (vNormSq v)
  | 0, Vec.nil => RatEq_refl _
  | Nat.succ _, Vec.cons x xs =>
      ratAdd_respects (conj_mul_self_re x) (cinner_self_re xs)

/-- **Vector Gram diagonal, imaginary part**: `⟨v,v⟩.im = 0`. -/
theorem cinner_self_im : {n : Nat} → (v : Vec n) → RatEq (cinner v v).im ratZero
  | 0, Vec.nil => RatEq_refl _
  | Nat.succ _, Vec.cons x xs =>
      RatEq_trans _ _ _
        (ratAdd_respects (conj_mul_self_im x) (cinner_self_im xs))
        (ratZero_add_left ratZero)

end BEDC.Derived.RHRoute.PassiveFiniteScatteringMatrix
