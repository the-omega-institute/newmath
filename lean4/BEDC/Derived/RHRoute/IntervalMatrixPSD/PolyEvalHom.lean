import BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator

/-
Narrow `ArchPoly` evaluation homomorphism (loop: archimedean obligation, block 7a).

`evalPoly` (from PolyPanelError, `evalShift 0`, right-oriented power
`pow x (n+1) = (pow x n) * x`) is a ring homomorphism on the concrete `ArchPoly = List BRat`
polynomial operations `polyAdd / polyScale / polyShift / polyMul` (ArchimedeanEntry).  These
reusable lemmas turn the `E1_4` polynomial identity (block 7b) into a finite coefficient
comparison instead of a degree-6 symbolic expansion (oracle conv_ff4ff126afd06e33).

Route + lemma shapes from the oracle; all proofs 0-axiom / propext-free, over Rat/List
*variables* only (no whnf blowup on concrete qNat terms — block-1 discipline).
-/

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyEvalHom

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.LocatedReal
open BEDC.Derived.RHRoute.IntervalMatrixPSD
open BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator

/-- Right-oriented one-step power unfold at the Rat *variable* level (opaque boundary). -/
private theorem pow_succ (x : Rat) (k : Nat) :
    RatEq (pow x (Nat.succ k)) (ratMul (pow x k) x) := by
  change RatEq (ratMul (pow x k) x) (ratMul (pow x k) x)
  exact RatEq_refl _

/-- Four-term additive shuffle `(a+b)+(c+d) = (a+c)+(b+d)`. -/
private theorem ratAdd_shuffle (a b c d : BRat) :
    RatEq (ratAdd (ratAdd a b) (ratAdd c d)) (ratAdd (ratAdd a c) (ratAdd b d)) :=
  RatEq_trans _ _ _ (ratAdd_assoc_local a b (ratAdd c d))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl a)
        (RatEq_trans _ _ _ (RatEq_symm (ratAdd_assoc_local b c d))
          (RatEq_trans _ _ _ (ratAdd_respects (ratAdd_comm b c) (RatEq_refl d))
            (ratAdd_assoc_local c b d))))
      (RatEq_symm (ratAdd_assoc_local a c (ratAdd b d))))

/-- `(P*t)*Q = (P*Q)*t`. -/
private theorem ratMul_swap_mid (P t Q : BRat) :
    RatEq (ratMul (ratMul P t) Q) (ratMul (ratMul P Q) t) :=
  RatEq_trans _ _ _ (ratMul_assoc P t Q)
    (RatEq_trans _ _ _ (ratMul_respects_right (ratMul_comm t Q))
      (RatEq_symm (ratMul_assoc P Q t)))

/-- `c*Q + (P*Q)*t = (c + P*t)*Q`  (the `polyMul` cons-step algebra). -/
private theorem evalPoly_mul_cons_algebra (c P Q t : BRat) :
    RatEq (ratAdd (ratMul c Q) (ratMul (ratMul P Q) t))
      (ratMul (ratAdd c (ratMul P t)) Q) :=
  RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl (ratMul c Q)) (RatEq_symm (ratMul_swap_mid P t Q)))
    (RatEq_symm (ratMul_add_right c (ratMul P t) Q))

/-- `evalShift (k+1) p t = (evalShift k p t) * t` (degree shift, right power). -/
theorem evalShift_succ_eq_mul_right (t : BRat) :
    ∀ (p : ArchPoly) (k : Nat),
      RatEq (evalShift (Nat.succ k) p t) (ratMul (evalShift k p t) t) := by
  intro p
  induction p with
  | nil => intro k; exact RatEq_symm (ratMul_zero_left t)
  | cons a as ih =>
      intro k
      exact RatEq_trans _ _ _
        (ratAdd_respects (ratMul_respects_right (pow_succ t k)) (ih (Nat.succ k)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_symm (ratMul_assoc a (pow t k) t)) (RatEq_refl _))
          (RatEq_symm
            (ratMul_add_right (ratMul a (pow t k)) (evalShift (Nat.succ k) as t) t)))

/-- Cons unfold at degree 0: `evalPoly (c :: p) t = c + (evalPoly p t) * t`. -/
theorem evalPoly_cons (c : BRat) (p : ArchPoly) (t : BRat) :
    RatEq (evalPoly (c :: p) t) (ratAdd c (ratMul (evalPoly p t) t)) :=
  ratAdd_respects (ratMul_one_right c) (evalShift_succ_eq_mul_right t p 0)

/-- `evalPoly (polyShift p) t = (evalPoly p t) * t`. -/
theorem evalPoly_polyShift (p : ArchPoly) (t : BRat) :
    RatEq (evalPoly (polyShift p) t) (ratMul (evalPoly p t) t) :=
  RatEq_trans _ _ _ (evalPoly_cons ratZero p t)
    (ratZero_add_left (ratMul (evalPoly p t) t))

/-- `evalPoly (polyScale c p) t = c * evalPoly p t`. -/
theorem evalPoly_polyScale (c : BRat) :
    ∀ (p : ArchPoly) (t : BRat),
      RatEq (evalPoly (polyScale c p) t) (ratMul c (evalPoly p t)) := by
  intro p
  induction p with
  | nil =>
      intro t
      exact RatEq_symm
        (RatEq_trans _ _ _ (ratMul_comm c ratZero) (ratMul_zero_left c))
  | cons a as ih =>
      intro t
      exact RatEq_trans _ _ _
        (evalPoly_cons (ratMul c a) (polyScale c as) t)
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl (ratMul c a))
            (RatEq_trans _ _ _ (ratMul_respects_left (ih t))
              (ratMul_assoc c (evalPoly as t) t)))
          (RatEq_trans _ _ _
            (RatEq_symm (ratMul_add_left c a (ratMul (evalPoly as t) t)))
            (ratMul_respects_right (RatEq_symm (evalPoly_cons a as t)))))

/-- `evalPoly (polyAdd p q) t = evalPoly p t + evalPoly q t`. -/
theorem evalPoly_polyAdd :
    ∀ (p q : ArchPoly) (t : BRat),
      RatEq (evalPoly (polyAdd p q) t) (ratAdd (evalPoly p t) (evalPoly q t)) := by
  intro p
  induction p with
  | nil => intro q t; exact RatEq_symm (ratZero_add_left (evalPoly q t))
  | cons a as ih =>
      intro q t
      cases q with
      | nil => exact RatEq_symm (ratAdd_zero_right (evalPoly (a :: as) t))
      | cons b bs =>
          exact RatEq_trans _ _ _
            (evalPoly_cons (ratAdd a b) (polyAdd as bs) t)
            (RatEq_trans _ _ _
              (ratAdd_respects (RatEq_refl (ratAdd a b))
                (RatEq_trans _ _ _ (ratMul_respects_left (ih bs t))
                  (ratMul_add_right (evalPoly as t) (evalPoly bs t) t)))
              (RatEq_trans _ _ _
                (ratAdd_shuffle a b (ratMul (evalPoly as t) t)
                  (ratMul (evalPoly bs t) t))
                (ratAdd_respects (RatEq_symm (evalPoly_cons a as t))
                  (RatEq_symm (evalPoly_cons b bs t)))))

/-- `evalPoly (polyMul p q) t = evalPoly p t * evalPoly q t`. -/
theorem evalPoly_polyMul :
    ∀ (p q : ArchPoly) (t : BRat),
      RatEq (evalPoly (polyMul p q) t) (ratMul (evalPoly p t) (evalPoly q t)) := by
  intro p
  induction p with
  | nil => intro q t; exact RatEq_symm (ratMul_zero_left (evalPoly q t))
  | cons c p ih =>
      intro q t
      -- polyMul (c :: p) q = polyAdd (polyScale c q) (polyShift (polyMul p q))
      exact RatEq_trans _ _ _
        (evalPoly_polyAdd (polyScale c q) (polyShift (polyMul p q)) t)
        (RatEq_trans _ _ _
          (ratAdd_respects (evalPoly_polyScale c q t)
            (RatEq_trans _ _ _ (evalPoly_polyShift (polyMul p q) t)
              (ratMul_respects_left (ih q t))))
          (RatEq_trans _ _ _
            (evalPoly_mul_cons_algebra c (evalPoly p t) (evalPoly q t) t)
            (ratMul_respects_left (RatEq_symm (evalPoly_cons c p t)))))

/-- `ratSub` respects `RatEq` on the right argument. -/
theorem ratSub_respects_right {a b c : BRat} (h : RatEq b c) :
    RatEq (ratSub a b) (ratSub a c) := by
  unfold ratSub
  exact ratAdd_respects (RatEq_refl a) (ratNeg_respects h)

end BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyEvalHom
