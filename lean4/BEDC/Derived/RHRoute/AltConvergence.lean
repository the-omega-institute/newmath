import BEDC.Derived.RHRoute.AlternatingTailBound
import BEDC.Derived.LocatedReal.ToleranceClose

set_option maxHeartbeats 1000000

namespace BEDC.Derived.RHRoute.AltConvergence

open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal
open BEDC.Derived.RHRoute.AlternatingTailBound
open BEDC.FKernel.Hist
open BEDC.Derived.PrimeUp

abbrev Rat := RatNum
abbrev RatInt := BEDC.Derived.PrimeUp.IntegerUp

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
  have aNorm : IntEq A A' := by
    exact R.mul_assoc xn yd zd
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

private theorem ratAdd_assoc_local (x y z : Rat) :
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

private theorem ratAdd_neg_local (x : Rat) :
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

private theorem ratNeg_add_local (x : Rat) :
    RatEq (ratAdd (ratNeg x) x) ratZero := by
  exact RatEq_trans _ _ _
    (ratAdd_comm (ratNeg x) x)
    (ratAdd_neg_local x)

private theorem ratNeg_neg_local (x : Rat) :
    RatEq (ratNeg (ratNeg x)) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_neg x.num
  · unfold ratNeg ratDenInt
    exact IntEq_refl (intOfNat x.den (ratDenCarrier (ratNeg (ratNeg x))))

private theorem ratNeg_add_dist_local (x y : Rat) :
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

private theorem ratSub_common_left {x x' y z : Rat} :
    RatEq x x' ->
      RatEq (ratSub (ratAdd x y) (ratAdd x' z)) (ratSub y z) := by
  intro sameCommon
  unfold ratSub
  have negExpand :
      RatEq (ratAdd (ratAdd x y) (ratNeg (ratAdd x' z)))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg z))) :=
    ratAdd_respects (RatEq_refl (ratAdd x y)) (ratNeg_add_dist_local x' z)
  have commonAligned :
      RatEq (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg z)))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x) (ratNeg z))) :=
    ratAdd_respects (RatEq_refl (ratAdd x y))
      (ratAdd_respects (ratNeg_respects (RatEq_symm sameCommon)) (RatEq_refl (ratNeg z)))
  have paired :
      RatEq (ratAdd (ratAdd x y) (ratAdd (ratNeg x) (ratNeg z)))
        (ratAdd (ratAdd x (ratNeg x)) (ratAdd y (ratNeg z))) := by
    exact RatEq_trans _ _ _
      (ratAdd_assoc_local x y (ratAdd (ratNeg x) (ratNeg z)))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x)
          (RatEq_symm (ratAdd_assoc_local y (ratNeg x) (ratNeg z))))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (ratAdd_respects (ratAdd_comm y (ratNeg x)) (RatEq_refl (ratNeg z))))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x)
              (ratAdd_assoc_local (ratNeg x) y (ratNeg z)))
            (RatEq_symm (ratAdd_assoc_local x (ratNeg x) (ratAdd y (ratNeg z)))))))
  exact RatEq_trans _ _ _ negExpand
    (RatEq_trans _ _ _ commonAligned
        (RatEq_trans _ _ _ paired
          (RatEq_trans _ _ _
            (ratAdd_respects (ratAdd_neg_local x) (RatEq_refl (ratAdd y (ratNeg z))))
            (ratZero_add_left (ratAdd y (ratNeg z))))))

private theorem ratSub_neg_neg {x y : Rat} :
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

private theorem ratAbs_respects {x y : Rat} :
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

private theorem ratAbs_sub_neg_neg_local {x y : Rat} :
    RatEq (ratAbs (ratSub (ratNeg x) (ratNeg y))) (ratAbs (ratSub x y)) := by
  exact RatEq_trans _ _ _
    (ratAbs_respects (ratSub_neg_neg (x := x) (y := y)))
    (ratAbs_neg (ratSub x y))

def etaPartial (a : Nat -> Rat) (N : Nat) : Rat :=
  altPartialSum a 0 N

private def signedByParity (n : Nat) (x : Rat) : Rat :=
  match n with
  | 0 => x
  | Nat.succ n => ratNeg (signedByParity n x)

private theorem Nat_zero_le_sub_of_le {n m : Nat} :
    n ≤ m -> n + (m - n) = m := by
  intro h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => cases h
  | succ m ih =>
      cases n with
      | zero =>
          rw [Nat.zero_add, Nat.sub_zero]
      | succ n =>
          rw [Nat.succ_sub_succ_eq_sub]
          rw [Nat.succ_add]
          exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem ratNeg_zero :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_zero_of_num_zero
  unfold ratNeg ratZero intToRat
  exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero

private theorem ratLe_of_abs_RatEq {x y z : Rat} :
    RatEq (ratAbs x) (ratAbs y) ->
      ratLe (ratAbs y) z -> ratLe (ratAbs x) z := by
  intro same h
  exact ratLe_respects (RatEq_symm same) (RatEq_refl z) h

private theorem ratDist_le_of_abs_sub_le {x y r : Rat} :
    ratLe (ratAbs (ratSub x y)) r -> ratLe (ratDist x y) r := by
  intro h
  exact h

private theorem ratDist_symm_le {x y r : Rat} :
    ratLe (ratDist x y) r -> ratLe (ratDist y x) r := by
  intro h
  exact ratLe_respects (ratDist_symm x y) (RatEq_refl r) h

private theorem signedByParity_abs (n : Nat) (x : Rat) :
    RatEq (ratAbs (signedByParity n x)) (ratAbs x) := by
  induction n with
  | zero =>
      exact RatEq_refl _
  | succ n ih =>
      exact RatEq_trans _ _ _
        (ratAbs_neg (signedByParity n x))
        ih

private theorem signedByParity_abs_respects {x y : Rat} (n : Nat) :
    RatEq x y ->
      RatEq (ratAbs (signedByParity n x)) (ratAbs (signedByParity n y)) := by
  intro h
  exact RatEq_trans _ _ _
    (signedByParity_abs n x)
    (RatEq_trans _ _ _ (ratAbs_respects h) (RatEq_symm (signedByParity_abs n y)))

private theorem nat_start_succ (N n : Nat) :
    N + Nat.succ n = (N + 1) + n := by
  calc
    N + Nat.succ n = N + (n + 1) := rfl
    _ = N + (1 + n) := congrArg (fun t => N + t) (Nat.add_comm n 1)
    _ = (N + 1) + n := (Nat.add_assoc N 1 n).symm

private theorem alt_tail_abs_identity (a : Nat -> Rat) (N n M : Nat) :
    RatEq
      (ratAbs (ratSub (altPartialSum a N (n + M)) (altPartialSum a N n)))
      (ratAbs (signedByParity n (altPartialSum a (N + n) M))) := by
  induction n generalizing N with
  | zero =>
      rw [Nat.zero_add, Nat.add_zero]
      change
        RatEq
          (ratAbs (ratSub (altPartialSum a N M) ratZero))
          (ratAbs (altPartialSum a N M))
      unfold ratSub
      exact RatEq_trans _ _ _
        (ratAbs_respects (ratAdd_respects (RatEq_refl (altPartialSum a N M)) ratNeg_zero))
        (ratAbs_respects (ratAdd_zero_right (altPartialSum a N M)))
  | succ n ih =>
      have succAdd : Nat.succ n + M = Nat.succ (n + M) := by
        exact Nat.succ_add n M
      rw [succAdd]
      change
        RatEq
          (ratAbs
            (ratSub
              (ratAdd (a N) (ratNeg (altPartialSum a (N + 1) (n + M))))
              (ratAdd (a N) (ratNeg (altPartialSum a (N + 1) n)))))
          (ratAbs (ratNeg (signedByParity n (altPartialSum a (N + Nat.succ n) M))))
      have common :
          RatEq
            (ratSub
              (ratAdd (a N) (ratNeg (altPartialSum a (N + 1) (n + M))))
              (ratAdd (a N) (ratNeg (altPartialSum a (N + 1) n))))
            (ratSub
              (ratNeg (altPartialSum a (N + 1) (n + M)))
              (ratNeg (altPartialSum a (N + 1) n))) :=
        ratSub_common_left (RatEq_refl (a N))
      have negAbs :
          RatEq
            (ratAbs
              (ratSub
                (ratNeg (altPartialSum a (N + 1) (n + M)))
                (ratNeg (altPartialSum a (N + 1) n))))
            (ratAbs
              (ratSub (altPartialSum a (N + 1) (n + M))
                (altPartialSum a (N + 1) n))) :=
        ratAbs_sub_neg_neg_local
      have tailShift :
          RatEq
            (ratAbs
              (ratSub (altPartialSum a (N + 1) (n + M))
                (altPartialSum a (N + 1) n)))
            (ratAbs (signedByParity n (altPartialSum a ((N + 1) + n) M))) :=
        ih (N := N + 1)
      have tailIndex :
          RatEq
            (altPartialSum a ((N + 1) + n) M)
            (altPartialSum a (N + Nat.succ n) M) := by
        rw [nat_start_succ N n]
        exact RatEq_refl _
      have tailCongr :
          RatEq
            (ratAbs (signedByParity n (altPartialSum a ((N + 1) + n) M)))
            (ratAbs (signedByParity n (altPartialSum a (N + Nat.succ n) M))) := by
        exact signedByParity_abs_respects n tailIndex
      exact RatEq_trans _ _ _
        (ratAbs_respects common)
        (RatEq_trans _ _ _ negAbs
          (RatEq_trans _ _ _ tailShift
            (RatEq_trans _ _ _ tailCongr
              (RatEq_symm
                (ratAbs_neg
                  (signedByParity n (altPartialSum a (N + Nat.succ n) M)))))))

private theorem eta_partial_tail_bound_forward
    (a : Nat -> Rat)
    (nonneg : forall n : Nat, ratLe ratZero (a n))
    (antitone : forall n : Nat, ratLe (a (n + 1)) (a n))
    (n m : Nat) (hnm : n ≤ m) :
    ratLe (ratAbs (ratSub (etaPartial a m) (etaPartial a n))) (a n) := by
  -- The algebraic tail identity is the only rational-group ingredient needed here.
  -- It is kept local to this node so the public API remains the convergence surface.
  let M := m - n
  have tailBound :
      ratLe (ratAbs (altPartialSum a n M)) (a n) :=
    alternating_tail_le_head a nonneg antitone n M
  have _mn : n + M = m := Nat_zero_le_sub_of_le hnm
  -- The current rational layer exposes order and metric primitives, but not yet
  -- a public additive-group normalization theorem for eta prefixes.  The
  -- following exact identity is the missing normalization target for this file.
  have same :
      RatEq (ratAbs (ratSub (etaPartial a m) (etaPartial a n)))
        (ratAbs (signedByParity n (altPartialSum a n M))) := by
    rw [← _mn]
    change
      RatEq
        (ratAbs (ratSub (altPartialSum a 0 (n + M)) (altPartialSum a 0 n)))
        (ratAbs (signedByParity n (altPartialSum a n M)))
    have raw := alt_tail_abs_identity a 0 n M
    rw [Nat.zero_add] at raw
    exact raw
  have signAbs :
      RatEq (ratAbs (signedByParity n (altPartialSum a n M)))
        (ratAbs (altPartialSum a n M)) := by
    exact signedByParity_abs n (altPartialSum a n M)
  exact ratLe_of_abs_RatEq (RatEq_trans _ _ _ same signAbs) tailBound

structure RatLeibnizData where
  a : Nat -> Rat
  nonneg : forall n : Nat, ratLe ratZero (a n)
  antitone : forall n : Nat, ratLe (a (n + 1)) (a n)
  zeroIndex : Nat -> Nat
  zeroIndex_mono : forall {i j : Nat}, i ≤ j -> zeroIndex i ≤ zeroIndex j
  zeroSpec :
    forall k n : Nat, zeroIndex k ≤ n -> ratLe (a n) (dyadicRat k)

def altSeqLReal (laws : RatToleranceCloseLaws) (D : RatLeibnizData) :
    Nat -> LReal (RatToleranceMetricKit laws) :=
  fun N => ratToLReal (RatToleranceMetricKit laws) (etaPartial D.a N)

def rat_alt_partial_cauchy
    (laws : RatToleranceCloseLaws) (D : RatLeibnizData) :
    LRealSeqCauchy (altSeqLReal laws D) := by
  exact {
    index := D.zeroIndex
    index_mono := by
      intro i j hij
      exact D.zeroIndex_mono hij
    cauchy := by
      intro k m n hm hn
      unfold altSeqLReal ratToLReal RatToleranceMetricKit ratToleranceClose
      cases Nat.le_total n m with
      | inl hnm =>
          have tail :
              ratLe
                (ratAbs (ratSub (etaPartial D.a m) (etaPartial D.a n)))
                (D.a n) :=
            eta_partial_tail_bound_forward D.a D.nonneg D.antitone n m hnm
          have distLe :
              ratLe (ratDist (etaPartial D.a m) (etaPartial D.a n)) (D.a n) :=
            ratDist_le_of_abs_sub_le tail
          have minSmallN : ratLe (D.a n) (dyadicRat k) :=
            D.zeroSpec k n hn
          exact ratLe_trans distLe
            minSmallN
      | inr hmn =>
          have tail :
              ratLe
                (ratAbs (ratSub (etaPartial D.a n) (etaPartial D.a m)))
                (D.a m) :=
            eta_partial_tail_bound_forward D.a D.nonneg D.antitone m n hmn
          have distForward :
              ratLe (ratDist (etaPartial D.a n) (etaPartial D.a m)) (D.a m) :=
            ratDist_le_of_abs_sub_le tail
          have distLe :
              ratLe (ratDist (etaPartial D.a m) (etaPartial D.a n)) (D.a m) :=
            ratDist_symm_le distForward
          have minSmallM : ratLe (D.a m) (dyadicRat k) :=
            D.zeroSpec k m hm
          exact ratLe_trans distLe
            minSmallM
  }

def altLimit (laws : RatToleranceCloseLaws) (D : RatLeibnizData) :
    LReal (RatToleranceMetricKit laws) :=
  lrLimit (altSeqLReal laws D) (rat_alt_partial_cauchy laws D)

end BEDC.Derived.RHRoute.AltConvergence
