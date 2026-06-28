import BEDC.Derived.PolynomialUp.Calculus

namespace BEDC.Derived.HermitePolynomialUp

open BEDC.Derived.PolynomialUp

abbrev IntegerUp := BEDC.Derived.PolynomialUp.IntegerUp
abbrev Poly := BEDC.Derived.PolynomialUp.Poly

private abbrev zZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

private abbrev zOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

private abbrev zAdd : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntAdd

private abbrev zMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntMul

private abbrev zNeg : IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntNeg

private abbrev zEq : IntegerUp -> IntegerUp -> Prop :=
  BEDC.Derived.RationalUp.IntEq

private abbrev zLaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

def monomialX : Poly :=
  [zZero, zOne]

def hermiteStep (n : Nat) (previous current : Poly) : Poly :=
  polyAdd (polyShift current)
    (polyScale (zNeg (coeffOfNat n)) previous)

def hermitePoly : Nat -> Poly
  | 0 => polyOne
  | 1 => monomialX
  | Nat.succ (Nat.succ n) =>
      hermiteStep (Nat.succ n) (hermitePoly n) (hermitePoly (Nat.succ n))

private theorem polyScale_succ_coeff (n : Nat) (p : Poly) :
    PolyEq (polyScale (coeffOfNat (Nat.succ n)) p)
      (polyAdd p (polyScale (coeffOfNat n) p)) := by
  intro k
  exact zLaws.eq_trans
    (polyCoeff_scale (coeffOfNat (Nat.succ n)) p k)
    (zLaws.eq_trans
      (coeffOfNat_succ_mul n (polyCoeff p k))
      (zLaws.eq_symm
        (zLaws.eq_trans (polyCoeff_add p (polyScale (coeffOfNat n) p) k)
          (zLaws.add_respects
            (zLaws.eq_refl (polyCoeff p k))
            (polyCoeff_scale (coeffOfNat n) p k)))))

private theorem polyScale_neg_coeff (a : IntegerUp) (p : Poly) :
    PolyEq (polyScale (zNeg a) p) (polyNeg (polyScale a p)) := by
  intro k
  exact zLaws.eq_trans (polyCoeff_scale (zNeg a) p k)
    (zLaws.eq_trans
      (BEDC.Algebra.Rel.IntegerUp_neg_mul a (polyCoeff p k))
      (zLaws.eq_trans
        (zLaws.neg_respects (zLaws.eq_symm (polyCoeff_scale a p k)))
        (zLaws.eq_symm (polyCoeff_neg (polyScale a p) k))))

theorem hermitePoly_zero :
    PolyEq (hermitePoly 0) polyOne :=
  PolyEq_refl polyOne

theorem hermitePoly_one :
    PolyEq (hermitePoly 1) monomialX :=
  PolyEq_refl monomialX

theorem hermitePoly_recurrence (n : Nat) :
    PolyEq (hermitePoly (Nat.succ (Nat.succ n)))
      (hermiteStep (Nat.succ n) (hermitePoly n) (hermitePoly (Nat.succ n))) :=
  PolyEq_refl _

private theorem polyDeriv_monomialX :
    PolyEq (polyDeriv monomialX) polyOne := by
  intro k
  cases k with
  | zero =>
      change zEq (zMul (coeffOfNat 1) zOne) zOne
      exact zLaws.one_mul zOne
  | succ k =>
      cases k with
      | zero =>
          change zEq zZero zZero
          exact zLaws.eq_refl zZero
      | succ k =>
          change zEq zZero zZero
          exact zLaws.eq_refl zZero

private theorem polyMul_monomialX (p : Poly) :
    PolyEq (polyMul monomialX p) (polyShift p) := by
  have mulRightOne :
      PolyEq (polyMul p [zOne]) p :=
    PolyEq_trans (polyMul_cons_right zOne [] p)
      (PolyEq_trans
        (polyAdd_right_zero_of_eqv
          (p := polyScale zOne p)
          (q := polyShift (polyMul p []))
          (polyShift_zero_of_eqv (polyMul_zero p)))
        (polyScale_one_left p))
  have mulRightX :
      PolyEq (polyMul p monomialX) (polyShift p) :=
    PolyEq_trans (polyMul_cons_right zZero [zOne] p)
      (PolyEq_trans
        (polyAdd_left_zero_of_eqv
          (p := polyScale zZero p)
          (q := polyShift (polyMul p [zOne]))
          (polyScale_zero_left p))
        (polyShift_respects mulRightOne))
  exact PolyEq_trans (polyMul_comm monomialX p) mulRightX

theorem hermitePoly_x_recurrence (n : Nat) :
    PolyEq (hermitePoly (Nat.succ (Nat.succ n)))
      (polyAdd (polyMul monomialX (hermitePoly (Nat.succ n)))
        (polyNeg (polyScale (coeffOfNat (Nat.succ n)) (hermitePoly n)))) := by
  exact PolyEq_trans (hermitePoly_recurrence n)
    (polyAdd_respects
      (PolyEq_symm (polyMul_monomialX (hermitePoly (Nat.succ n))))
      (polyScale_neg_coeff (coeffOfNat (Nat.succ n)) (hermitePoly n)))

theorem hermitePoly_two :
    PolyEq (hermitePoly 2)
      (polyAdd (polyMul monomialX monomialX)
        (polyNeg (polyScale (coeffOfNat 1) polyOne))) :=
  hermitePoly_x_recurrence 0

private theorem polyScale_neg_left_scale (a b : IntegerUp) (p : Poly) :
    PolyEq (polyScale (zNeg a) (polyScale b p))
      (polyScale a (polyScale (zNeg b) p)) := by
  exact PolyEq_trans
    (PolyEq_symm (polyScale_scale (zNeg a) b p))
    (PolyEq_trans
      (polyScale_respects
        (BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_neg_commuted a b)
        (PolyEq_refl p))
      (polyScale_scale a (zNeg b) p))

private theorem polyScale_hermiteStep (a : IntegerUp) (n : Nat)
    (previous current : Poly) :
    PolyEq (polyScale a (hermiteStep n previous current))
      (polyAdd (polyShift (polyScale a current))
        (polyScale a (polyScale (zNeg (coeffOfNat n)) previous))) := by
  unfold hermiteStep
  exact PolyEq_trans
    (polyScale_add a (polyShift current)
      (polyScale (zNeg (coeffOfNat n)) previous))
    (polyAdd_respects (polyScale_shift a current)
      (PolyEq_refl (polyScale a (polyScale (zNeg (coeffOfNat n)) previous))))

private theorem hermitePoly_deriv_step {n : Nat}
    (older previous current : Poly)
    (currentStep : PolyEq current (hermiteStep n older previous))
    (dprevious : PolyEq (polyDeriv previous) (polyScale (coeffOfNat n) older))
    (dcurrent : PolyEq (polyDeriv current)
      (polyScale (coeffOfNat (Nat.succ n)) previous)) :
    PolyEq (polyDeriv (hermiteStep (Nat.succ n) previous current))
      (polyScale (coeffOfNat (Nat.succ (Nat.succ n))) current) := by
  let a := coeffOfNat (Nat.succ n)
  let b := coeffOfNat n
  have derivNormal :
      PolyEq (polyDeriv (hermiteStep (Nat.succ n) previous current))
        (polyAdd
          (polyAdd current (polyShift (polyScale a previous)))
          (polyScale (zNeg a) (polyScale b older))) := by
    unfold hermiteStep
    exact PolyEq_trans
      (polyDeriv_add (polyShift current) (polyScale (zNeg a) previous))
      (PolyEq_trans
        (polyAdd_respects (polyDeriv_shift current)
          (polyDeriv_scale (zNeg a) previous))
        (polyAdd_respects
          (polyAdd_respects (PolyEq_refl current) (polyShift_respects dcurrent))
          (polyScale_respects (zLaws.eq_refl (zNeg a)) dprevious)))
  have scaleCurrent :
      PolyEq (polyScale a current)
        (polyAdd (polyShift (polyScale a previous))
          (polyScale (zNeg a) (polyScale b older))) :=
    (PolyEq_trans
      (polyScale_respects (zLaws.eq_refl a) currentStep)
      (PolyEq_trans
        (polyScale_hermiteStep a n older previous)
        (polyAdd_respects
          (PolyEq_refl (polyShift (polyScale a previous)))
          (PolyEq_symm (polyScale_neg_left_scale a b older)))))
  exact PolyEq_trans derivNormal
    (PolyEq_trans
      (polyAdd_assoc current (polyShift (polyScale a previous))
        (polyScale (zNeg a) (polyScale b older)))
      (PolyEq_trans
        (polyAdd_respects (PolyEq_refl current) (PolyEq_symm scaleCurrent))
        (PolyEq_trans
          (PolyEq_symm (polyScale_succ_coeff (Nat.succ n) current))
          (PolyEq_refl (polyScale (coeffOfNat (Nat.succ (Nat.succ n))) current)))))

private theorem hermitePoly_one_as_step_zero :
    PolyEq monomialX (hermiteStep 0 polyZero polyOne) := by
  exact PolyEq_refl monomialX

theorem hermitePoly_deriv :
    ∀ n : Nat,
      PolyEq (polyDeriv (hermitePoly (Nat.succ n)))
        (polyScale (coeffOfNat (Nat.succ n)) (hermitePoly n))
  | 0 =>
      PolyEq_trans polyDeriv_monomialX
        (PolyEq_symm (polyScale_one_left polyOne))
  | Nat.succ 0 =>
      hermitePoly_deriv_step
        (n := 0)
        polyZero polyOne monomialX
        hermitePoly_one_as_step_zero
        (PolyEq_refl polyZero)
        (PolyEq_trans polyDeriv_monomialX
          (PolyEq_symm (polyScale_one_left polyOne)))
  | Nat.succ (Nat.succ n) =>
      hermitePoly_deriv_step
        (n := Nat.succ n)
        (hermitePoly n)
        (hermitePoly (Nat.succ n))
        (hermitePoly (Nat.succ (Nat.succ n)))
        (PolyEq_refl (hermitePoly (Nat.succ (Nat.succ n))))
        (hermitePoly_deriv n)
        (hermitePoly_deriv (Nat.succ n))

end BEDC.Derived.HermitePolynomialUp
