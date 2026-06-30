import BEDC.Derived.LocatedReal.GroundedDyadic

set_option maxHeartbeats 1000000

namespace BEDC.Derived.LocatedReal

open BEDC.Derived.RationalUp
open BEDC.Derived.PrimeUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)

private abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

theorem dyadic_nonneg (k : Nat) :
    ratLe ratZero (dyadicRat k) := by
  apply ratNonneg_of_num
  unfold dyadicRat
  change intLe intZero intOne
  exact intLe_zero_of_nat BEDC.Derived.PadicUp.NatOne
    (BEDC.FKernel.Unary.unary_e1_closed BEDC.FKernel.Unary.unary_empty)

theorem ratToleranceClose_refl (x : Rat) (k : Nat) :
    ratToleranceClose x x k := by
  unfold ratToleranceClose
  exact ratLe_trans
    (ratLe_of_RatEq (ratDist_self x))
    (dyadic_nonneg k)

theorem ratToleranceClose_symm {x y : Rat} {k : Nat} :
    ratToleranceClose x y k -> ratToleranceClose y x k := by
  intro h
  unfold ratToleranceClose at h ⊢
  exact ratLe_trans (ratLe_of_RatEq (RatEq_symm (ratDist_symm x y))) h

private theorem ratEq_zero_of_num_zero {x : Rat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem intAdd_four_swap (a b c d : RatInt) :
    IntEq (IntAdd (IntAdd a b) (IntAdd c d))
      (IntAdd (IntAdd a c) (IntAdd b d)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  exact R.trans (R.add_assoc a b (IntAdd c d))
    (R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc b c d)))
      (R.trans
        (R.add_congr (R.refl a)
          (R.add_congr (R.add_comm b c) (R.refl d)))
        (R.trans
          (R.add_congr (R.refl a) (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (IntAdd b d))))))

private theorem intNeg_add_local (a b : RatInt) :
    IntEq (IntNeg (IntAdd a b)) (IntAdd (IntNeg a) (IntNeg b)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  have paired :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b)))
        (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b))) :=
    intAdd_four_swap a b (IntNeg a) (IntNeg b)
  have collapsed :
      IntEq (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b)))
        (IntAdd intZero intZero) :=
    IntAdd_respects (IntAdd_neg a) (IntAdd_neg b)
  have zeroed :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b))) intZero :=
    IntEq_trans paired (IntEq_trans collapsed (IntAdd_zero_left intZero))
  exact IntEq_symm
    (R.eq_neg_of_add_eq_zero (a := IntAdd a b)
      (b := IntAdd (IntNeg a) (IntNeg b)) zeroed)

private theorem ratDenInt_neg_local (x : Rat) :
    IntEq (ratDenInt (ratNeg x)) (ratDenInt x) := by
  unfold ratDenInt ratNeg
  exact IntEq_refl (intOfNat x.den (ratDenCarrier x))

private theorem intRatAddAssocNum
    (xn xd yn yd zn zd : RatInt) :
    IntEq
      (IntAdd
        (IntMul (IntAdd (IntMul xn yd) (IntMul yn xd)) zd)
        (IntMul zn (IntMul xd yd)))
      (IntAdd
        (IntMul xn (IntMul yd zd))
        (IntMul (IntAdd (IntMul yn zd) (IntMul zn yd)) xd)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  let A := IntMul (IntMul xn yd) zd
  let B := IntMul (IntMul yn xd) zd
  let C := IntMul zn (IntMul xd yd)
  let A' := IntMul xn (IntMul yd zd)
  let B' := IntMul (IntMul yn zd) xd
  let C' := IntMul (IntMul zn yd) xd
  have expandLeft :
      IntEq
        (IntAdd
          (IntMul (IntAdd (IntMul xn yd) (IntMul yn xd)) zd)
          (IntMul zn (IntMul xd yd)))
        (IntAdd (IntAdd A B) C) := by
    exact R.add_congr
      (R.right_distrib (IntMul xn yd) (IntMul yn xd) zd)
      (R.refl C)
  have aNorm : IntEq A A' :=
    R.mul_assoc xn yd zd
  have bNorm : IntEq B B' := by
    exact R.trans (R.mul_assoc yn xd zd)
      (R.trans
        (R.mul_congr (R.refl yn) (R.mul_comm xd zd))
        (R.symm (R.mul_assoc yn zd xd)))
  have cNorm : IntEq C C' := by
    exact R.trans
      (R.mul_congr (R.refl zn) (R.mul_comm xd yd))
      (R.symm (R.mul_assoc zn yd xd))
  have regroup :
      IntEq (IntAdd (IntAdd A B) C)
        (IntAdd A' (IntAdd B' C')) := by
    exact R.trans (R.add_assoc A B C)
      (R.add_congr aNorm (R.add_congr bNorm cNorm))
  have foldRight :
      IntEq (IntAdd A' (IntAdd B' C'))
        (IntAdd
          (IntMul xn (IntMul yd zd))
          (IntMul (IntAdd (IntMul yn zd) (IntMul zn yd)) xd)) := by
    exact R.add_congr (R.refl A')
      (R.symm (R.right_distrib (IntMul yn zd) (IntMul zn yd) xd))
  exact R.trans expandLeft (R.trans regroup foldRight)

theorem ratAdd_assoc_local (x y z : Rat) :
    RatEq (ratAdd (ratAdd x y) z) (ratAdd x (ratAdd y z)) := by
  apply ratEq_of_num_den_intEq
  · have leftToStructured :
        IntEq (ratAdd (ratAdd x y) z).num
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (IntMul (ratDenInt x) (ratDenInt y)))) := by
      unfold ratAdd
      change
        IntEq
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (ratDenInt (ratAdd x y))))
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (IntMul (ratDenInt x) (ratDenInt y))))
      exact IntAdd_respects (IntEq_refl _)
        (IntMul_respects (IntEq_refl z.num) (ratDenInt_add x y))
    have rightToStructured :
        IntEq (ratAdd x (ratAdd y z)).num
          (IntAdd
            (IntMul x.num (IntMul (ratDenInt y) (ratDenInt z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x))) := by
      unfold ratAdd
      change
        IntEq
          (IntAdd
            (IntMul x.num (ratDenInt (ratAdd y z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x)))
          (IntAdd
            (IntMul x.num (IntMul (ratDenInt y) (ratDenInt z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x)))
      exact IntAdd_respects
        (IntMul_respects (IntEq_refl x.num) (ratDenInt_add y z))
        (IntEq_refl _)
    exact IntEq_trans leftToStructured
      (IntEq_trans
        (intRatAddAssocNum x.num (ratDenInt x) y.num (ratDenInt y)
          z.num (ratDenInt z))
        (IntEq_symm rightToStructured))
  · have leftDen :
        IntEq (ratDenInt (ratAdd (ratAdd x y) z))
          (IntMul (IntMul (ratDenInt x) (ratDenInt y)) (ratDenInt z)) := by
      exact IntEq_trans (ratDenInt_add (ratAdd x y) z)
        (IntMul_respects (ratDenInt_add x y) (IntEq_refl (ratDenInt z)))
    have rightDen :
        IntEq (ratDenInt (ratAdd x (ratAdd y z)))
          (IntMul (ratDenInt x) (IntMul (ratDenInt y) (ratDenInt z))) := by
      exact IntEq_trans (ratDenInt_add x (ratAdd y z))
        (IntMul_respects (IntEq_refl (ratDenInt x)) (ratDenInt_add y z))
    exact IntEq_trans leftDen
      (IntEq_trans (IntMul_assoc (ratDenInt x) (ratDenInt y) (ratDenInt z))
        (IntEq_symm rightDen))

theorem ratAdd_neg_local (x : Rat) :
    RatEq (ratAdd x (ratNeg x)) ratZero := by
  apply ratEq_zero_of_num_zero
  unfold ratAdd ratNeg
  change
    IntEq
      (IntAdd (IntMul x.num (ratDenInt (ratNeg x)))
        (IntMul (IntNeg x.num) (ratDenInt x))) intZero
  have leftDen :
      IntEq (IntMul x.num (ratDenInt (ratNeg x)))
        (IntMul x.num (ratDenInt x)) :=
    IntMul_respects (IntEq_refl x.num) (ratDenInt_neg_local x)
  have rightNeg :
      IntEq (IntMul (IntNeg x.num) (ratDenInt x))
        (IntNeg (IntMul x.num (ratDenInt x))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt x)
  exact IntEq_trans (IntAdd_respects leftDen rightNeg)
    (IntAdd_neg (IntMul x.num (ratDenInt x)))

theorem ratNeg_add_local (x : Rat) :
    RatEq (ratAdd (ratNeg x) x) ratZero := by
  exact RatEq_trans _ _ _
    (ratAdd_comm (ratNeg x) x)
    (ratAdd_neg_local x)

theorem ratNeg_neg_local (x : Rat) :
    RatEq (ratNeg (ratNeg x)) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_neg x.num
  · unfold ratNeg ratDenInt
    exact IntEq_refl (intOfNat x.den (ratDenCarrier (ratNeg (ratNeg x))))

theorem ratNeg_add_dist_local (x y : Rat) :
    RatEq (ratNeg (ratAdd x y)) (ratAdd (ratNeg x) (ratNeg y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratAdd
    change
      IntEq
        (IntNeg
          (IntAdd (IntMul x.num (ratDenInt y))
            (IntMul y.num (ratDenInt x))))
        (IntAdd
          (IntMul (IntNeg x.num) (ratDenInt (ratNeg y)))
          (IntMul (IntNeg y.num) (ratDenInt (ratNeg x))))
    have leftNeg :
        IntEq
          (IntNeg
            (IntAdd (IntMul x.num (ratDenInt y))
              (IntMul y.num (ratDenInt x))))
          (IntAdd
            (IntNeg (IntMul x.num (ratDenInt y)))
            (IntNeg (IntMul y.num (ratDenInt x)))) :=
      intNeg_add_local (IntMul x.num (ratDenInt y))
        (IntMul y.num (ratDenInt x))
    have first :
        IntEq (IntNeg (IntMul x.num (ratDenInt y)))
          (IntMul (IntNeg x.num) (ratDenInt (ratNeg y))) := by
      exact IntEq_trans
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)))
        (IntMul_respects (IntEq_refl (IntNeg x.num))
          (IntEq_symm (ratDenInt_neg_local y)))
    have second :
        IntEq (IntNeg (IntMul y.num (ratDenInt x)))
          (IntMul (IntNeg y.num) (ratDenInt (ratNeg x))) := by
      exact IntEq_trans
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)))
        (IntMul_respects (IntEq_refl (IntNeg y.num))
          (IntEq_symm (ratDenInt_neg_local x)))
    exact IntEq_trans leftNeg (IntAdd_respects first second)
  · unfold ratNeg
    exact IntEq_trans (ratDenInt_neg_local (ratAdd x y))
      (IntEq_trans (ratDenInt_add x y)
        (IntEq_trans
          (IntMul_respects (IntEq_symm (ratDenInt_neg_local x))
            (IntEq_symm (ratDenInt_neg_local y)))
          (IntEq_symm (ratDenInt_add (ratNeg x) (ratNeg y)))))

theorem ratSub_neg_neg (x y : Rat) :
    RatEq (ratSub (ratNeg x) (ratNeg y)) (ratNeg (ratSub x y)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl (ratNeg x)) (ratNeg_neg_local y))
    (RatEq_trans _ _ _
      (RatEq_symm
        (ratAdd_respects (RatEq_refl (ratNeg x)) (ratNeg_neg_local y)))
      (RatEq_symm (ratNeg_add_dist_local x (ratNeg y))))

private theorem ratAbs_neg (x : Rat) :
    RatEq (ratAbs (ratNeg x)) (ratAbs x) := by
  unfold ratAbs
  exact ratMagnitude_neg x

private theorem ratAbs_cross_left (x y : Rat) :
    IntEq
      (IntMul (ratAbs x).num (ratDenInt (ratAbs y)))
      (intOfNat (IntMul x.num (ratDenInt y)).magnitude
        (IntMul x.num (ratDenInt y)).carrier.right) := by
  unfold ratAbs ratMagnitude
  have product :
      NatMul x.num.magnitude y.den
        (IntMul x.num (ratDenInt y)).magnitude := by
    have raw := intMul_magnitude_natMul x.num (ratDenInt y)
    unfold ratDenInt intOfNat at raw
    exact raw
  have canonical :
      NatMul x.num.magnitude y.den
        (BEDC.Derived.IntUp.natMulFn x.num.magnitude y.den) :=
    BEDC.Derived.IntUp.natMulFn_rel x.num.carrier.right (ratDenCarrier y)
  have sameProduct :
      hsame (BEDC.Derived.IntUp.natMulFn x.num.magnitude y.den)
        (IntMul x.num (ratDenInt y)).magnitude :=
    NatMul_functional x.num.carrier.right canonical product
  have toCanonical :
      IntEq
        (IntMul (intOfNat x.num.magnitude x.num.carrier.right)
          (intOfNat y.den (ratDenCarrier y)))
        (intOfNat (BEDC.Derived.IntUp.natMulFn x.num.magnitude y.den)
          (BEDC.Derived.IntUp.natMulFn_unary x.num.carrier.right (ratDenCarrier y))) :=
    IntEq_symm
      (intOfNat_natMul_as_intMul x.num.magnitude y.den
        x.num.carrier.right (ratDenCarrier y)
        (BEDC.Derived.IntUp.natMulFn_unary x.num.carrier.right (ratDenCarrier y)))
  have canonicalToCross :
      IntEq
        (intOfNat (BEDC.Derived.IntUp.natMulFn x.num.magnitude y.den)
          (BEDC.Derived.IntUp.natMulFn_unary x.num.carrier.right (ratDenCarrier y)))
        (intOfNat (IntMul x.num (ratDenInt y)).magnitude
          (IntMul x.num (ratDenInt y)).carrier.right) :=
    intOfNat_hsame_congr
      (BEDC.Derived.IntUp.natMulFn_unary x.num.carrier.right (ratDenCarrier y))
      (IntMul x.num (ratDenInt y)).carrier.right
      sameProduct
  exact IntEq_trans toCanonical canonicalToCross

theorem ratAbs_respects {x y : Rat} :
    RatEq x y -> RatEq (ratAbs x) (ratAbs y) := by
  intro same
  unfold RatEq at same ⊢
  change
    IntEq
      (IntMul (ratAbs x).num (ratDenInt (ratAbs y)))
      (IntMul (ratAbs y).num (ratDenInt (ratAbs x)))
  have left := ratAbs_cross_left x y
  have right := ratAbs_cross_left y x
  have magSame :
      IntEq
        (intOfNat (IntMul x.num (ratDenInt y)).magnitude
          (IntMul x.num (ratDenInt y)).carrier.right)
        (intOfNat (IntMul y.num (ratDenInt x)).magnitude
          (IntMul y.num (ratDenInt x)).carrier.right) :=
    intOfNat_hsame_congr
      (IntMul x.num (ratDenInt y)).carrier.right
      (IntMul y.num (ratDenInt x)).carrier.right
      (IntEq_magnitude_hsame same)
  exact IntEq_trans left (IntEq_trans magSame (IntEq_symm right))

theorem ratDist_neg (x y : Rat) :
    RatEq (ratDist (ratNeg x) (ratNeg y)) (ratDist x y) := by
  unfold ratDist
  exact RatEq_trans _ _ _
    (ratAbs_respects (ratSub_neg_neg x y))
    (ratAbs_neg (ratSub x y))

private theorem powTwoNat_monotone {lo hi : Nat} :
    lo <= hi -> powTwoNat lo <= powTwoNat hi := by
  intro h
  induction hi generalizing lo with
  | zero =>
      cases lo with
      | zero => exact Nat.le_refl _
      | succ lo => cases h
  | succ hi ih =>
      cases lo with
      | zero =>
          exact Nat.le_trans (Nat.le_refl 1) (powTwoNat_pos (Nat.succ hi))
      | succ lo =>
          change 2 * powTwoNat lo <= 2 * powTwoNat hi
          exact Nat.mul_le_mul_left 2 (ih (Nat.le_of_succ_le_succ h))

theorem dyadic_monotone {lo hi : Nat} :
    lo <= hi -> ratLe (dyadicRat hi) (dyadicRat lo) := by
  intro h
  unfold ratLe
  have base :
      intLe (ratDenInt (dyadicRat lo)) (ratDenInt (dyadicRat hi)) := by
    unfold ratDenInt dyadicRat
    apply intOfNat_le_of_nat_le
    change
      bwordLength (BEDC.Derived.IntUp.natToUnary (powTwoNat lo)) <=
        bwordLength (BEDC.Derived.IntUp.natToUnary (powTwoNat hi))
    rw [BEDC.Derived.IntUp.natToUnary_length,
      BEDC.Derived.IntUp.natToUnary_length]
    exact powTwoNat_monotone h
  exact intLe_respects
    (IntEq_symm (intMul_one_left (ratDenInt (dyadicRat lo))))
    (IntEq_symm (intMul_one_left (ratDenInt (dyadicRat hi))))
    base

theorem ratZero_sub_eq_neg (x : Rat) :
    RatEq (ratSub ratZero x) (ratNeg x) := by
  unfold ratSub
  exact ratZero_add_left (ratNeg x)

theorem ratSub_add_sub_left_cancel (x x' y : Rat) :
    RatEq (ratSub (ratAdd x' y) (ratSub x' x)) (ratAdd x y) := by
  unfold ratSub
  have negExpand :
      RatEq
        (ratAdd (ratAdd x' y) (ratNeg (ratAdd x' (ratNeg x))))
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') (ratNeg (ratNeg x)))) :=
    ratAdd_respects (RatEq_refl _) (ratNeg_add_dist_local x' (ratNeg x))
  have negNeg :
      RatEq
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') (ratNeg (ratNeg x))))
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') x)) :=
    ratAdd_respects (RatEq_refl _) (ratAdd_respects (RatEq_refl _) (ratNeg_neg_local x))
  have paired :
      RatEq
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') x))
        (ratAdd (ratAdd x' (ratNeg x')) (ratAdd y x)) := by
    exact RatEq_trans _ _ _
      (ratAdd_assoc_local x' y (ratAdd (ratNeg x') x))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x')
          (RatEq_symm (ratAdd_assoc_local y (ratNeg x') x)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x')
            (ratAdd_respects (ratAdd_comm y (ratNeg x')) (RatEq_refl x)))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x')
              (ratAdd_assoc_local (ratNeg x') y x))
            (RatEq_symm (ratAdd_assoc_local x' (ratNeg x') (ratAdd y x))))))
  exact RatEq_trans _ _ _ negExpand
    (RatEq_trans _ _ _ negNeg
      (RatEq_trans _ _ _ paired
        (RatEq_trans _ _ _
          (ratAdd_respects (ratAdd_neg_local x') (RatEq_refl (ratAdd y x)))
          (RatEq_trans _ _ _
            (ratZero_add_left (ratAdd y x))
            (ratAdd_comm y x)))))

theorem ratLe_add_right_mono {x x' y : Rat} :
    ratLe x x' -> ratLe (ratAdd x y) (ratAdd x' y) := by
  intro h
  have diffNonneg : ratLe ratZero (ratSub x' x) :=
    ratSub_nonneg_of_le h
  have base :
      ratLe (ratSub (ratAdd x' y) (ratSub x' x)) (ratAdd x' y) :=
    ratSub_le_left_of_nonneg diffNonneg
  exact ratLe_respects
    (ratSub_add_sub_left_cancel x x' y)
    (RatEq_refl _)
    base

theorem ratLe_add_left_mono {y y' x : Rat} :
    ratLe y y' -> ratLe (ratAdd x y) (ratAdd x y') := by
  intro h
  exact ratLe_respects
    (ratAdd_comm y x)
    (ratAdd_comm y' x)
    (ratLe_add_right_mono (x := y) (x' := y') (y := x) h)

theorem ratLe_add_mono {x x' y y' : Rat} :
    ratLe x x' -> ratLe y y' ->
      ratLe (ratAdd x y) (ratAdd x' y') := by
  intro hx hy
  exact ratLe_trans
    (ratLe_add_right_mono (x := x) (x' := x') (y := y) hx)
    (ratLe_add_left_mono (y := y) (y' := y') (x := x') hy)

private theorem ratAbs_eq_self_of_nonneg {x : Rat} :
    ratLe ratZero x -> RatEq (ratAbs x) x := by
  intro h
  unfold ratAbs
  exact ratMagnitude_eq_self_of_nonneg h

private theorem ratNeg_nonneg_of_nonpos {x : Rat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _) (ratZero_sub_eq_neg x) subNonneg

private theorem ratAbs_eq_neg_of_nonpos {x : Rat} :
    ratLe x ratZero -> RatEq (ratAbs x) (ratNeg x) := by
  intro h
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAbs_neg x))
    (ratAbs_eq_self_of_nonneg (ratNeg_nonneg_of_nonpos h))

theorem ratLe_self_abs (x : Rat) :
    ratLe x (ratAbs x) := by
  cases ratLe_total ratZero x with
  | inl h0 =>
      exact ratLe_of_RatEq (RatEq_symm (ratAbs_eq_self_of_nonneg h0))
  | inr hx =>
      exact ratLe_trans hx (ratMagnitude_nonneg x)

theorem ratLe_neg_abs (x : Rat) :
    ratLe (ratNeg x) (ratAbs x) := by
  cases ratLe_total ratZero x with
  | inl h0 =>
      have negLeZeroSub : ratLe (ratSub ratZero x) ratZero :=
        ratSub_le_left_of_nonneg h0
      have negLeZero : ratLe (ratNeg x) ratZero :=
        ratLe_respects (ratZero_sub_eq_neg x) (RatEq_refl _) negLeZeroSub
      exact ratLe_trans negLeZero (ratMagnitude_nonneg x)
  | inr hx =>
      exact ratLe_of_RatEq (RatEq_symm (ratAbs_eq_neg_of_nonpos hx))

theorem ratAbs_triangle (a b : Rat) :
    ratLe (ratAbs (ratAdd a b)) (ratAdd (ratAbs a) (ratAbs b)) := by
  have upper :
      ratLe (ratAdd a b) (ratAdd (ratAbs a) (ratAbs b)) :=
    ratLe_add_mono (ratLe_self_abs a) (ratLe_self_abs b)
  have negUpperRaw :
      ratLe (ratAdd (ratNeg a) (ratNeg b)) (ratAdd (ratAbs a) (ratAbs b)) :=
    ratLe_add_mono (ratLe_neg_abs a) (ratLe_neg_abs b)
  have negUpper :
      ratLe (ratNeg (ratAdd a b)) (ratAdd (ratAbs a) (ratAbs b)) :=
    ratLe_respects
      (RatEq_symm (ratNeg_add_dist_local a b))
      (RatEq_refl _)
      negUpperRaw
  cases ratLe_total ratZero (ratAdd a b) with
  | inl hnonneg =>
      exact ratAbs_le_of_nonneg_le hnonneg upper
  | inr hnonpos =>
      exact ratLe_respects
        (RatEq_symm (ratAbs_eq_neg_of_nonpos hnonpos))
        (RatEq_refl _)
        negUpper

theorem ratSub_add_decomp (x y z : Rat) :
    RatEq (ratSub x z) (ratAdd (ratSub x y) (ratSub y z)) := by
  unfold ratSub
  have step1 :
      RatEq (ratAdd (ratAdd x (ratNeg y)) (ratAdd y (ratNeg z)))
        (ratAdd x (ratAdd (ratNeg y) (ratAdd y (ratNeg z)))) :=
    ratAdd_assoc_local x (ratNeg y) (ratAdd y (ratNeg z))
  have step2 :
      RatEq (ratAdd x (ratAdd (ratNeg y) (ratAdd y (ratNeg z))))
        (ratAdd x (ratAdd (ratAdd (ratNeg y) y) (ratNeg z))) :=
    ratAdd_respects (RatEq_refl x)
      (RatEq_symm (ratAdd_assoc_local (ratNeg y) y (ratNeg z)))
  have step3 :
      RatEq (ratAdd x (ratAdd (ratAdd (ratNeg y) y) (ratNeg z)))
        (ratAdd x (ratAdd ratZero (ratNeg z))) :=
    ratAdd_respects (RatEq_refl x)
      (ratAdd_respects (ratNeg_add_local y) (RatEq_refl (ratNeg z)))
  have step4 :
      RatEq (ratAdd x (ratAdd ratZero (ratNeg z)))
        (ratAdd x (ratNeg z)) :=
    ratAdd_respects (RatEq_refl x) (ratZero_add_left (ratNeg z))
  exact RatEq_symm
    (RatEq_trans _ _ _ step1
      (RatEq_trans _ _ _ step2
        (RatEq_trans _ _ _ step3 step4)))

theorem ratDist_triangle (x y z : Rat) :
    ratLe (ratDist x z) (ratAdd (ratDist x y) (ratDist y z)) := by
  unfold ratDist
  exact ratLe_respects
    (ratAbs_respects (RatEq_symm (ratSub_add_decomp x y z)))
    (RatEq_refl _)
    (ratAbs_triangle (ratSub x y) (ratSub y z))

private theorem ratSub_add_add_common (x x' y y' : Rat) :
    RatEq (ratSub (ratAdd x y) (ratAdd x' y'))
      (ratAdd (ratSub x x') (ratSub y y')) := by
  unfold ratSub
  have negExpand :
      RatEq
        (ratAdd (ratAdd x y) (ratNeg (ratAdd x' y')))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg y'))) :=
    ratAdd_respects (RatEq_refl _) (ratNeg_add_dist_local x' y')
  have regroup :
      RatEq
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg y')))
        (ratAdd (ratAdd x (ratNeg x')) (ratAdd y (ratNeg y'))) := by
    exact RatEq_trans _ _ _
      (ratAdd_assoc_local x y (ratAdd (ratNeg x') (ratNeg y')))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x)
          (RatEq_symm (ratAdd_assoc_local y (ratNeg x') (ratNeg y'))))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (ratAdd_respects (ratAdd_comm y (ratNeg x')) (RatEq_refl (ratNeg y'))))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x)
              (ratAdd_assoc_local (ratNeg x') y (ratNeg y')))
            (RatEq_symm (ratAdd_assoc_local x (ratNeg x') (ratAdd y (ratNeg y')))))))
  exact RatEq_trans _ _ _ negExpand regroup

theorem ratDist_add_le (x x' y y' : Rat) :
    ratLe (ratDist (ratAdd x y) (ratAdd x' y'))
      (ratAdd (ratDist x x') (ratDist y y')) := by
  unfold ratDist
  exact ratLe_respects
    (ratAbs_respects (RatEq_symm (ratSub_add_add_common x x' y y')))
    (RatEq_refl _)
    (ratAbs_triangle (ratSub x x') (ratSub y y'))

def groundedRatToleranceLaws : RatToleranceCloseLaws where
  close_refl := ratToleranceClose_refl
  close_symm := by
    intro x y k
    exact ratToleranceClose_symm
  close_weaken := by
    intro x y hi lo hlo h
    unfold ratToleranceClose at h ⊢
    exact ratLe_trans h (dyadic_monotone hlo)
  close_triangle := by
    intro x y z k xy yz
    unfold ratToleranceClose at xy yz ⊢
    have distBound :
        ratLe (ratDist x z)
          (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k))) :=
      ratLe_trans (ratDist_triangle x y z)
        (ratLe_add_mono xy yz)
    exact ratLe_trans distBound (dyadic_succ_add k)
  eq_close := by
    intro x y h k
    unfold ratToleranceClose
    exact ratLe_trans
      (ratLe_of_RatEq ((ratDist_zero_iff x y).mpr h))
      (dyadic_nonneg k)
  add_close := by
    intro x x' y y' k xx yy
    unfold ratToleranceClose at xx yy ⊢
    have distBound :
        ratLe (ratDist (ratAdd x y) (ratAdd x' y'))
          (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k))) :=
      ratLe_trans (ratDist_add_le x x' y y')
        (ratLe_add_mono xx yy)
    exact ratLe_trans distBound (dyadic_succ_add k)
  neg_close := by
    intro x y k h
    unfold ratToleranceClose at h ⊢
    exact ratLe_trans
      (ratLe_of_RatEq (ratDist_neg x y))
      h

end BEDC.Derived.LocatedReal
