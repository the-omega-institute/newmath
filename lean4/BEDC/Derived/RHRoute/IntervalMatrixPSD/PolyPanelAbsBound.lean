import BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanEntry

/-
Reusable interval-arithmetic producer for `PolyAbsBoundSound` (loop: archimedean
obligation, block 2).

`PolyAbsBoundSound` (ArchimedeanEntry) was previously only ever consumed as a hypothesis,
never produced.  This file supplies the missing producer: on a nonneg-left closed panel
`[a, b]` (`0 <= a`), the absolute value of a polynomial is bounded by the abs-coefficient
polynomial evaluated at the right endpoint `b`.  With it, the concrete
`*_abs_bound_zeroPanel` obligations of `KernelApproxCerts.K1ZeroPanelObligations` (bounds on
`evalPoly K1_T` / `evalPoly K1_E1_4` over the zero panel `[0, 1/8]`) reduce to a single
rational comparison `evalPoly (map ratAbs coeffs) (1/8) <= bound` — the exact endpoint sum
the tree's `K1_T_abs_bound = 1633/3072` was designed around
(`1633 = 1536 + 96 + 1`, cf. `K1_T_abs_bound_raw_term_sum`).

All proofs 0-axiom / propext-free: triangle inequality (`ratAbs_triangle`), the monomial
power bound (`abs_pow_le`, `ratAbs_mul_le`), additive monotonicity (`ratAdd_le_add`) and
RatEq transport (`ratMagnitude_eq_self_of_nonneg`).  No ∀-t analytic / located-Γ / RH
content: this is a finite structural interval bound.
-/

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyPanelAbsBound

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.LocatedReal
open BEDC.Derived.RHRoute.IntervalMatrixPSD

/-- `|evalShift d cs t| <= evalShift d (map ratAbs cs) B` whenever `|t| <= B` and `0 <= B`.
Structural induction on the coefficient list: the triangle inequality splits the head
monomial `c * t^d` from the tail, `ratAbs_mul_le` + `abs_pow_le` bound the head by
`|c| * B^d`, and the induction hypothesis (at shift `d+1`) bounds the tail. -/
theorem evalShift_ratAbs_le
    (t B : BRat) (hB : ratLe ratZero B) (ht : ratLe (ratAbs t) B) :
    ∀ (cs : List BRat) (d : Nat),
      ratLe (ratAbs (evalShift d cs t)) (evalShift d (List.map ratAbs cs) B) := by
  intro cs
  induction cs with
  | nil =>
      intro _d
      exact ratLe_of_RatEq (ratMagnitude_eq_self_of_nonneg (ratLe_refl ratZero))
  | cons c cs ih =>
      intro d
      exact ratLe_trans
        (ratAbs_triangle (ratMul c (pow t d)) (evalShift (Nat.succ d) cs t))
        (ratAdd_le_add
          (ratAbs_mul_le (ratLe_refl (ratAbs c)) (abs_pow_le t B hB ht d))
          (ih (Nat.succ d)))

/-- Polynomial specialization (`evalPoly = evalShift 0`). -/
theorem evalPoly_ratAbs_le
    (cs : List BRat) (t B : BRat)
    (hB : ratLe ratZero B) (ht : ratLe (ratAbs t) B) :
    ratLe (ratAbs (evalPoly cs t)) (evalPoly (List.map ratAbs cs) B) :=
  evalShift_ratAbs_le t B hB ht cs 0

/-- Producer for `PolyAbsBoundSound`: on a panel `[a, b]` with `0 <= a`, a bound on the
abs-coefficient polynomial at the right endpoint `b` bounds `|evalPoly cs t|` for every
panel point `t`.  This is the reusable brick the concrete `*_abs_bound_zeroPanel`
obligations consume. -/
theorem polyAbsBoundSound_of_endpoint
    (cs : List BRat) (a b BA : BRat)
    (ha : ratLe ratZero a) (hb : ratLe ratZero b)
    (hbound : ratLe (evalPoly (List.map ratAbs cs) b) BA) :
    PolyAbsBoundSound cs a b BA := by
  intro t ht
  have tNonneg : ratLe ratZero t := ratLe_trans ha ht.1
  have tAbsLeB : ratLe (ratAbs t) b :=
    ratLe_respects
      (RatEq_symm (ratMagnitude_eq_self_of_nonneg tNonneg))
      (RatEq_refl b) ht.2
  exact ratLe_trans (evalPoly_ratAbs_le cs t b hb tAbsLeB) hbound

/-- A polynomial with nonnegative coefficients is nonnegative at a nonnegative point:
`0 <= evalShift d cs t` whenever `0 <= t` and every coefficient is `>= 0`.  The dual of
`evalShift_ratAbs_le` (a lower-bound producer): the reusable brick behind polynomial lower
bounds like `A_ge_one` for the rational-carrier zero-panel obligations. -/
theorem evalShift_nonneg (t : BRat) (ht : ratLe ratZero t) :
    ∀ (cs : List BRat), (∀ c, c ∈ cs → ratLe ratZero c) →
      ∀ d, ratLe ratZero (evalShift d cs t) := by
  intro cs
  induction cs with
  | nil => intro _ _d; exact ratLe_refl ratZero
  | cons c cs ih =>
      intro hc d
      have hterm : ratLe ratZero (ratMul c (pow t d)) :=
        ratMul_nonneg (hc c List.mem_cons_self) (ratPow_nonneg ht d)
      have hrest : ratLe ratZero (evalShift (Nat.succ d) cs t) :=
        ih (fun c' hc' => hc c' (List.mem_cons_of_mem c hc')) (Nat.succ d)
      exact ratLe_respects (ratAdd_zero_right ratZero) (RatEq_refl _)
        (ratAdd_le_add hterm hrest)

/-- Polynomial specialization of `evalShift_nonneg` (`evalPoly = evalShift 0`). -/
theorem evalPoly_nonneg (cs : List BRat) (t : BRat)
    (ht : ratLe ratZero t) (hc : ∀ c, c ∈ cs → ratLe ratZero c) :
    ratLe ratZero (evalPoly cs t) :=
  evalShift_nonneg t ht cs hc 0

end BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyPanelAbsBound
