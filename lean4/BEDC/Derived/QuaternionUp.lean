import BEDC.Algebra.FiniteFold
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.QuaternionUp

abbrev IntegerUp := BEDC.Derived.PrimeUp.IntegerUp
abbrev IntEq := BEDC.Derived.RationalUp.IntEq
abbrev intZero := BEDC.Derived.RationalUp.intZero
abbrev intOne := BEDC.Derived.RationalUp.intOne
abbrev IntAdd := BEDC.Derived.RationalUp.IntAdd
abbrev IntMul := BEDC.Derived.RationalUp.IntMul
abbrev IntNeg := BEDC.Derived.RationalUp.IntNeg

infix:50 " ≈z " => IntEq

instance intEqTrans : Trans IntEq IntEq IntEq where
  trans := by
    intro a b c
    exact BEDC.Derived.RationalUp.IntEq_trans

structure Quat where
  re : IntegerUp
  imI : IntegerUp
  imJ : IntegerUp
  imK : IntegerUp

def QuatEq (x y : Quat) : Prop :=
  x.re ≈z y.re ∧ x.imI ≈z y.imI ∧ x.imJ ≈z y.imJ ∧ x.imK ≈z y.imK

def quatZero : Quat :=
  { re := intZero, imI := intZero, imJ := intZero, imK := intZero }

def quatOne : Quat :=
  { re := intOne, imI := intZero, imJ := intZero, imK := intZero }

def quatAdd (x y : Quat) : Quat :=
  { re := IntAdd x.re y.re
    imI := IntAdd x.imI y.imI
    imJ := IntAdd x.imJ y.imJ
    imK := IntAdd x.imK y.imK }

def quatNeg (x : Quat) : Quat :=
  { re := IntNeg x.re
    imI := IntNeg x.imI
    imJ := IntNeg x.imJ
    imK := IntNeg x.imK }

def quatConj (x : Quat) : Quat :=
  { re := x.re
    imI := IntNeg x.imI
    imJ := IntNeg x.imJ
    imK := IntNeg x.imK }

private def zSub (x y : IntegerUp) : IntegerUp :=
  IntAdd x (IntNeg y)

private def zSquare (x : IntegerUp) : IntegerUp :=
  IntMul x x

private def zSum4 (a b c d : IntegerUp) : IntegerUp :=
  IntAdd (IntAdd a b) (IntAdd c d)

def quatMul (x y : Quat) : Quat :=
  { re := zSub (zSub (zSub (IntMul x.re y.re) (IntMul x.imI y.imI))
      (IntMul x.imJ y.imJ)) (IntMul x.imK y.imK)
    imI := IntAdd (IntAdd (IntMul x.re y.imI) (IntMul x.imI y.re))
      (zSub (IntMul x.imJ y.imK) (IntMul x.imK y.imJ))
    imJ := IntAdd (zSub (IntMul x.re y.imJ) (IntMul x.imI y.imK))
      (IntAdd (IntMul x.imJ y.re) (IntMul x.imK y.imI))
    imK := IntAdd (IntAdd (IntMul x.re y.imK) (IntMul x.imI y.imJ))
      (zSub (IntMul x.imK y.re) (IntMul x.imJ y.imI)) }

def quatNorm (x : Quat) : IntegerUp :=
  zSum4 (zSquare x.re) (zSquare x.imI) (zSquare x.imJ) (zSquare x.imK)

private theorem zEq_refl (x : IntegerUp) : x ≈z x :=
  BEDC.Derived.RationalUp.IntEq_refl x

private theorem zEq_symm {x y : IntegerUp} : x ≈z y -> y ≈z x :=
  BEDC.Derived.RationalUp.IntEq_symm

private theorem zEq_trans {x y z : IntegerUp} : x ≈z y -> y ≈z z -> x ≈z z :=
  BEDC.Derived.RationalUp.IntEq_trans

private theorem zAdd_respects {a a' b b' : IntegerUp} :
    a ≈z a' -> b ≈z b' -> IntAdd a b ≈z IntAdd a' b' :=
  BEDC.Derived.RationalUp.IntAdd_respects

private theorem zMul_respects {a a' b b' : IntegerUp} :
    a ≈z a' -> b ≈z b' -> IntMul a b ≈z IntMul a' b' :=
  BEDC.Derived.RationalUp.IntMul_respects

private theorem zNeg_respects {a b : IntegerUp} :
    a ≈z b -> IntNeg a ≈z IntNeg b :=
  BEDC.Derived.RationalUp.IntNeg_respects

private theorem zAdd_comm (a b : IntegerUp) : IntAdd a b ≈z IntAdd b a :=
  BEDC.Derived.RationalUp.IntAdd_comm a b

private theorem zAdd_assoc (a b c : IntegerUp) :
    IntAdd (IntAdd a b) c ≈z IntAdd a (IntAdd b c) :=
  BEDC.Derived.RationalUp.IntAdd_assoc a b c

private theorem zAdd_zero (a : IntegerUp) : IntAdd a intZero ≈z a :=
  BEDC.Derived.RationalUp.IntAdd_zero a

private theorem zZero_add (a : IntegerUp) : IntAdd intZero a ≈z a :=
  BEDC.Derived.RationalUp.IntAdd_zero_left a

private theorem zAdd_neg (a : IntegerUp) : IntAdd a (IntNeg a) ≈z intZero :=
  BEDC.Derived.RationalUp.IntAdd_neg a

private theorem zNeg_add (a : IntegerUp) : IntAdd (IntNeg a) a ≈z intZero :=
  BEDC.Derived.RationalUp.IntAdd_neg_left a

private theorem zMul_comm (a b : IntegerUp) : IntMul a b ≈z IntMul b a :=
  BEDC.Derived.RationalUp.IntMul_comm a b

private theorem zMul_assoc (a b c : IntegerUp) :
    IntMul (IntMul a b) c ≈z IntMul a (IntMul b c) :=
  BEDC.Derived.RationalUp.IntMul_assoc a b c

private theorem zMul_one (a : IntegerUp) : IntMul a intOne ≈z a :=
  BEDC.Derived.RationalUp.IntMul_one a

private theorem zOne_mul (a : IntegerUp) : IntMul intOne a ≈z a :=
  BEDC.Derived.RationalUp.IntMul_one_left a

private theorem zMul_zero (a : IntegerUp) : IntMul a intZero ≈z intZero :=
  BEDC.Derived.RationalUp.IntMul_zero a

private theorem zZero_mul (a : IntegerUp) : IntMul intZero a ≈z intZero :=
  BEDC.Derived.RationalUp.IntMul_zero_left a

private theorem zMul_add_distrib (a b c : IntegerUp) :
    IntMul a (IntAdd b c) ≈z IntAdd (IntMul a b) (IntMul a c) :=
  BEDC.Derived.RationalUp.IntMul_add_distrib a b c

private theorem zAdd_mul_distrib (a b c : IntegerUp) :
    IntMul (IntAdd a b) c ≈z IntAdd (IntMul a c) (IntMul b c) :=
  BEDC.Derived.RationalUp.IntMul_add_distrib_right a b c

private theorem zSub_respects {a a' b b' : IntegerUp} :
    a ≈z a' -> b ≈z b' -> zSub a b ≈z zSub a' b' := by
  intro ha hb
  exact zAdd_respects ha (zNeg_respects hb)

private theorem zNeg_zero : IntNeg intZero ≈z intZero := by
  calc
    IntNeg intZero ≈z IntAdd intZero (IntNeg intZero) := zEq_symm (zZero_add (IntNeg intZero))
    _ ≈z IntAdd (IntNeg intZero) intZero := zAdd_comm intZero (IntNeg intZero)
    _ ≈z intZero := zNeg_add intZero

private theorem zSub_zero (a : IntegerUp) : zSub a intZero ≈z a := by
  calc
    zSub a intZero ≈z IntAdd a intZero := zAdd_respects (zEq_refl a) zNeg_zero
    _ ≈z a := zAdd_zero a

private theorem zZero_sub (a : IntegerUp) : zSub intZero a ≈z IntNeg a := by
  exact zZero_add (IntNeg a)

private theorem zSub_self (a : IntegerUp) : zSub a a ≈z intZero :=
  zAdd_neg a

private theorem zAdd_zero_zero : IntAdd intZero intZero ≈z intZero :=
  zZero_add intZero

private theorem zAdd_zero_pair (a b : IntegerUp) :
    IntAdd (IntAdd intZero a) b ≈z IntAdd a b := by
  exact zAdd_respects (zZero_add a) (zEq_refl b)

private theorem zMul_zero_zero_sub : zSub intZero intZero ≈z intZero := by
  exact zSub_zero intZero

theorem QuatEq_refl (x : Quat) : QuatEq x x := by
  exact ⟨zEq_refl x.re, zEq_refl x.imI, zEq_refl x.imJ, zEq_refl x.imK⟩

theorem QuatEq_symm {x y : Quat} : QuatEq x y -> QuatEq y x := by
  intro h
  exact ⟨zEq_symm h.left, zEq_symm h.right.left,
    zEq_symm h.right.right.left, zEq_symm h.right.right.right⟩

theorem QuatEq_trans {x y z : Quat} : QuatEq x y -> QuatEq y z -> QuatEq x z := by
  intro hxy hyz
  exact ⟨zEq_trans hxy.left hyz.left,
    zEq_trans hxy.right.left hyz.right.left,
    zEq_trans hxy.right.right.left hyz.right.right.left,
    zEq_trans hxy.right.right.right hyz.right.right.right⟩

theorem quatAdd_respects {x x' y y' : Quat} :
    QuatEq x x' -> QuatEq y y' -> QuatEq (quatAdd x y) (quatAdd x' y') := by
  intro hx hy
  exact ⟨zAdd_respects hx.left hy.left,
    zAdd_respects hx.right.left hy.right.left,
    zAdd_respects hx.right.right.left hy.right.right.left,
    zAdd_respects hx.right.right.right hy.right.right.right⟩

theorem quatNeg_respects {x y : Quat} :
    QuatEq x y -> QuatEq (quatNeg x) (quatNeg y) := by
  intro h
  exact ⟨zNeg_respects h.left, zNeg_respects h.right.left,
    zNeg_respects h.right.right.left, zNeg_respects h.right.right.right⟩

theorem quatConj_respects {x y : Quat} :
    QuatEq x y -> QuatEq (quatConj x) (quatConj y) := by
  intro h
  exact ⟨h.left, zNeg_respects h.right.left,
    zNeg_respects h.right.right.left, zNeg_respects h.right.right.right⟩

theorem quatMul_respects {x x' y y' : Quat} :
    QuatEq x x' -> QuatEq y y' -> QuatEq (quatMul x y) (quatMul x' y') := by
  intro hx hy
  exact
    ⟨zSub_respects
        (zSub_respects
          (zSub_respects (zMul_respects hx.left hy.left)
            (zMul_respects hx.right.left hy.right.left))
          (zMul_respects hx.right.right.left hy.right.right.left))
        (zMul_respects hx.right.right.right hy.right.right.right),
      zAdd_respects
        (zAdd_respects (zMul_respects hx.left hy.right.left)
          (zMul_respects hx.right.left hy.left))
        (zSub_respects (zMul_respects hx.right.right.left hy.right.right.right)
          (zMul_respects hx.right.right.right hy.right.right.left)),
      zAdd_respects
        (zSub_respects (zMul_respects hx.left hy.right.right.left)
          (zMul_respects hx.right.left hy.right.right.right))
        (zAdd_respects (zMul_respects hx.right.right.left hy.left)
          (zMul_respects hx.right.right.right hy.right.left)),
      zAdd_respects
        (zAdd_respects (zMul_respects hx.left hy.right.right.right)
          (zMul_respects hx.right.left hy.right.right.left))
        (zSub_respects (zMul_respects hx.right.right.right hy.left)
          (zMul_respects hx.right.right.left hy.right.left))⟩

theorem quatAdd_comm (x y : Quat) : QuatEq (quatAdd x y) (quatAdd y x) := by
  exact ⟨zAdd_comm x.re y.re, zAdd_comm x.imI y.imI,
    zAdd_comm x.imJ y.imJ, zAdd_comm x.imK y.imK⟩

theorem quatAdd_assoc (x y z : Quat) :
    QuatEq (quatAdd (quatAdd x y) z) (quatAdd x (quatAdd y z)) := by
  exact ⟨zAdd_assoc x.re y.re z.re, zAdd_assoc x.imI y.imI z.imI,
    zAdd_assoc x.imJ y.imJ z.imJ, zAdd_assoc x.imK y.imK z.imK⟩

theorem quatAdd_zero (x : Quat) : QuatEq (quatAdd x quatZero) x := by
  exact ⟨zAdd_zero x.re, zAdd_zero x.imI, zAdd_zero x.imJ, zAdd_zero x.imK⟩

theorem quatZero_add (x : Quat) : QuatEq (quatAdd quatZero x) x := by
  exact ⟨zZero_add x.re, zZero_add x.imI, zZero_add x.imJ, zZero_add x.imK⟩

theorem quatAdd_neg (x : Quat) : QuatEq (quatAdd x (quatNeg x)) quatZero := by
  exact ⟨zAdd_neg x.re, zAdd_neg x.imI, zAdd_neg x.imJ, zAdd_neg x.imK⟩

theorem quatNeg_add (x : Quat) : QuatEq (quatAdd (quatNeg x) x) quatZero := by
  exact ⟨zNeg_add x.re, zNeg_add x.imI, zNeg_add x.imJ, zNeg_add x.imK⟩

private theorem quatMul_one_re (x : Quat) :
    (quatMul x quatOne).re ≈z x.re := by
  calc
    (quatMul x quatOne).re ≈z zSub (zSub (zSub x.re intZero) intZero) intZero :=
      zSub_respects
        (zSub_respects
          (zSub_respects (zMul_one x.re) (zMul_zero x.imI))
          (zMul_zero x.imJ))
        (zMul_zero x.imK)
    _ ≈z zSub (zSub x.re intZero) intZero := zSub_zero (zSub (zSub x.re intZero) intZero)
    _ ≈z zSub x.re intZero := zSub_zero (zSub x.re intZero)
    _ ≈z x.re := zSub_zero x.re

private theorem quatMul_one_imI (x : Quat) :
    (quatMul x quatOne).imI ≈z x.imI := by
  calc
    (quatMul x quatOne).imI ≈z IntAdd (IntAdd intZero x.imI) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zMul_zero x.re) (zMul_one x.imI))
        (zSub_respects (zMul_zero x.imJ) (zMul_zero x.imK))
    _ ≈z IntAdd (IntAdd intZero x.imI) intZero :=
      zAdd_respects (zEq_refl (IntAdd intZero x.imI)) zMul_zero_zero_sub
    _ ≈z IntAdd intZero x.imI := zAdd_zero (IntAdd intZero x.imI)
    _ ≈z x.imI := zZero_add x.imI

private theorem quatMul_one_imJ (x : Quat) :
    (quatMul x quatOne).imJ ≈z x.imJ := by
  calc
    (quatMul x quatOne).imJ ≈z IntAdd (zSub intZero intZero) (IntAdd x.imJ intZero) :=
      zAdd_respects
        (zSub_respects (zMul_zero x.re) (zMul_zero x.imI))
        (zAdd_respects (zMul_one x.imJ) (zMul_zero x.imK))
    _ ≈z IntAdd intZero (IntAdd x.imJ intZero) :=
      zAdd_respects zMul_zero_zero_sub (zEq_refl (IntAdd x.imJ intZero))
    _ ≈z IntAdd x.imJ intZero := zZero_add (IntAdd x.imJ intZero)
    _ ≈z x.imJ := zAdd_zero x.imJ

private theorem quatMul_one_imK (x : Quat) :
    (quatMul x quatOne).imK ≈z x.imK := by
  calc
    (quatMul x quatOne).imK ≈z IntAdd (IntAdd intZero intZero) (zSub x.imK intZero) :=
      zAdd_respects
        (zAdd_respects (zMul_zero x.re) (zMul_zero x.imI))
        (zSub_respects (zMul_one x.imK) (zMul_zero x.imJ))
    _ ≈z IntAdd intZero (zSub x.imK intZero) :=
      zAdd_respects zAdd_zero_zero (zEq_refl (zSub x.imK intZero))
    _ ≈z zSub x.imK intZero := zZero_add (zSub x.imK intZero)
    _ ≈z x.imK := zSub_zero x.imK

theorem quatMul_one (x : Quat) : QuatEq (quatMul x quatOne) x := by
  exact ⟨quatMul_one_re x, quatMul_one_imI x, quatMul_one_imJ x, quatMul_one_imK x⟩

private theorem quatOne_mul_re (x : Quat) :
    (quatMul quatOne x).re ≈z x.re := by
  calc
    (quatMul quatOne x).re ≈z zSub (zSub (zSub x.re intZero) intZero) intZero :=
      zSub_respects
        (zSub_respects
          (zSub_respects (zOne_mul x.re) (zZero_mul x.imI))
          (zZero_mul x.imJ))
        (zZero_mul x.imK)
    _ ≈z zSub (zSub x.re intZero) intZero := zSub_zero (zSub (zSub x.re intZero) intZero)
    _ ≈z zSub x.re intZero := zSub_zero (zSub x.re intZero)
    _ ≈z x.re := zSub_zero x.re

private theorem quatOne_mul_imI (x : Quat) :
    (quatMul quatOne x).imI ≈z x.imI := by
  calc
    (quatMul quatOne x).imI ≈z IntAdd (IntAdd x.imI intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zOne_mul x.imI) (zZero_mul x.re))
        (zSub_respects (zZero_mul x.imK) (zZero_mul x.imJ))
    _ ≈z IntAdd (IntAdd x.imI intZero) intZero :=
      zAdd_respects (zEq_refl (IntAdd x.imI intZero)) zMul_zero_zero_sub
    _ ≈z IntAdd x.imI intZero := zAdd_zero (IntAdd x.imI intZero)
    _ ≈z x.imI := zAdd_zero x.imI

private theorem quatOne_mul_imJ (x : Quat) :
    (quatMul quatOne x).imJ ≈z x.imJ := by
  calc
    (quatMul quatOne x).imJ ≈z IntAdd (zSub x.imJ intZero) (IntAdd intZero intZero) :=
      zAdd_respects
        (zSub_respects (zOne_mul x.imJ) (zZero_mul x.imK))
        (zAdd_respects (zZero_mul x.re) (zZero_mul x.imI))
    _ ≈z IntAdd (zSub x.imJ intZero) intZero :=
      zAdd_respects (zEq_refl (zSub x.imJ intZero)) zAdd_zero_zero
    _ ≈z zSub x.imJ intZero := zAdd_zero (zSub x.imJ intZero)
    _ ≈z x.imJ := zSub_zero x.imJ

private theorem quatOne_mul_imK (x : Quat) :
    (quatMul quatOne x).imK ≈z x.imK := by
  calc
    (quatMul quatOne x).imK ≈z IntAdd (IntAdd x.imK intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zOne_mul x.imK) (zZero_mul x.imJ))
        (zSub_respects (zZero_mul x.re) (zZero_mul x.imI))
    _ ≈z IntAdd (IntAdd x.imK intZero) intZero :=
      zAdd_respects (zEq_refl (IntAdd x.imK intZero)) zMul_zero_zero_sub
    _ ≈z IntAdd x.imK intZero := zAdd_zero (IntAdd x.imK intZero)
    _ ≈z x.imK := zAdd_zero x.imK

theorem quatOne_mul (x : Quat) : QuatEq (quatMul quatOne x) x := by
  exact ⟨quatOne_mul_re x, quatOne_mul_imI x, quatOne_mul_imJ x, quatOne_mul_imK x⟩

private theorem quatMul_zero_re (x : Quat) :
    (quatMul x quatZero).re ≈z intZero := by
  calc
    (quatMul x quatZero).re ≈z zSub (zSub (zSub intZero intZero) intZero) intZero :=
      zSub_respects
        (zSub_respects
          (zSub_respects (zMul_zero x.re) (zMul_zero x.imI))
          (zMul_zero x.imJ))
        (zMul_zero x.imK)
    _ ≈z zSub (zSub intZero intZero) intZero := zSub_zero (zSub (zSub intZero intZero) intZero)
    _ ≈z zSub intZero intZero := zSub_zero (zSub intZero intZero)
    _ ≈z intZero := zSub_zero intZero

private theorem quatMul_zero_imI (x : Quat) :
    (quatMul x quatZero).imI ≈z intZero := by
  calc
    (quatMul x quatZero).imI ≈z IntAdd (IntAdd intZero intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zMul_zero x.re) (zMul_zero x.imI))
        (zSub_respects (zMul_zero x.imJ) (zMul_zero x.imK))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zAdd_zero_zero zMul_zero_zero_sub
    _ ≈z intZero := zAdd_zero_zero

private theorem quatMul_zero_imJ (x : Quat) :
    (quatMul x quatZero).imJ ≈z intZero := by
  calc
    (quatMul x quatZero).imJ ≈z IntAdd (zSub intZero intZero) (IntAdd intZero intZero) :=
      zAdd_respects
        (zSub_respects (zMul_zero x.re) (zMul_zero x.imI))
        (zAdd_respects (zMul_zero x.imJ) (zMul_zero x.imK))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zMul_zero_zero_sub zAdd_zero_zero
    _ ≈z intZero := zAdd_zero_zero

private theorem quatMul_zero_imK (x : Quat) :
    (quatMul x quatZero).imK ≈z intZero := by
  calc
    (quatMul x quatZero).imK ≈z IntAdd (IntAdd intZero intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zMul_zero x.re) (zMul_zero x.imI))
        (zSub_respects (zMul_zero x.imK) (zMul_zero x.imJ))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zAdd_zero_zero zMul_zero_zero_sub
    _ ≈z intZero := zAdd_zero_zero

theorem quatMul_zero (x : Quat) : QuatEq (quatMul x quatZero) quatZero := by
  exact ⟨quatMul_zero_re x, quatMul_zero_imI x, quatMul_zero_imJ x, quatMul_zero_imK x⟩

private theorem quatZero_mul_re (x : Quat) :
    (quatMul quatZero x).re ≈z intZero := by
  calc
    (quatMul quatZero x).re ≈z zSub (zSub (zSub intZero intZero) intZero) intZero :=
      zSub_respects
        (zSub_respects
          (zSub_respects (zZero_mul x.re) (zZero_mul x.imI))
          (zZero_mul x.imJ))
        (zZero_mul x.imK)
    _ ≈z zSub (zSub intZero intZero) intZero := zSub_zero (zSub (zSub intZero intZero) intZero)
    _ ≈z zSub intZero intZero := zSub_zero (zSub intZero intZero)
    _ ≈z intZero := zSub_zero intZero

private theorem quatZero_mul_imI (x : Quat) :
    (quatMul quatZero x).imI ≈z intZero := by
  calc
    (quatMul quatZero x).imI ≈z IntAdd (IntAdd intZero intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zZero_mul x.imI) (zZero_mul x.re))
        (zSub_respects (zZero_mul x.imK) (zZero_mul x.imJ))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zAdd_zero_zero zMul_zero_zero_sub
    _ ≈z intZero := zAdd_zero_zero

private theorem quatZero_mul_imJ (x : Quat) :
    (quatMul quatZero x).imJ ≈z intZero := by
  calc
    (quatMul quatZero x).imJ ≈z IntAdd (zSub intZero intZero) (IntAdd intZero intZero) :=
      zAdd_respects
        (zSub_respects (zZero_mul x.imJ) (zZero_mul x.imK))
        (zAdd_respects (zZero_mul x.re) (zZero_mul x.imI))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zMul_zero_zero_sub zAdd_zero_zero
    _ ≈z intZero := zAdd_zero_zero

private theorem quatZero_mul_imK (x : Quat) :
    (quatMul quatZero x).imK ≈z intZero := by
  calc
    (quatMul quatZero x).imK ≈z IntAdd (IntAdd intZero intZero) (zSub intZero intZero) :=
      zAdd_respects
        (zAdd_respects (zZero_mul x.imK) (zZero_mul x.imJ))
        (zSub_respects (zZero_mul x.re) (zZero_mul x.imI))
    _ ≈z IntAdd intZero intZero :=
      zAdd_respects zAdd_zero_zero zMul_zero_zero_sub
    _ ≈z intZero := zAdd_zero_zero

theorem quatZero_mul (x : Quat) : QuatEq (quatMul quatZero x) quatZero := by
  exact ⟨quatZero_mul_re x, quatZero_mul_imI x, quatZero_mul_imJ x, quatZero_mul_imK x⟩

theorem quatNorm_respects {x y : Quat} :
    QuatEq x y -> quatNorm x ≈z quatNorm y := by
  intro h
  exact zAdd_respects
    (zAdd_respects (zMul_respects h.left h.left)
      (zMul_respects h.right.left h.right.left))
    (zAdd_respects (zMul_respects h.right.right.left h.right.right.left)
      (zMul_respects h.right.right.right h.right.right.right))

private def zring : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem zNeg_neg (a : IntegerUp) : IntNeg (IntNeg a) ≈z a :=
  zring.neg_neg a

private theorem zEq_neg_of_add_eq_zero {a b : IntegerUp} :
    IntAdd a b ≈z intZero -> b ≈z IntNeg a := by
  intro h
  exact zring.eq_neg_of_add_eq_zero h

private theorem zNeg_add_pair (a b : IntegerUp) :
    IntNeg (IntAdd a b) ≈z IntAdd (IntNeg a) (IntNeg b) := by
  have hzero :
      IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b)) ≈z intZero := by
    calc
      IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b))
          ≈z IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b)) :=
            zring.trans (zring.add_assoc a b (IntAdd (IntNeg a) (IntNeg b)))
              (zring.trans
                (zring.add_congr (zEq_refl a)
                  (zring.symm (zring.add_assoc b (IntNeg a) (IntNeg b))))
                (zring.trans
                  (zring.add_congr (zEq_refl a)
                    (zring.add_congr (zring.add_comm b (IntNeg a))
                      (zEq_refl (IntNeg b))))
                  (zring.trans
                    (zring.add_congr (zEq_refl a)
                      (zring.add_assoc (IntNeg a) b (IntNeg b)))
                    (zring.symm (zring.add_assoc a (IntNeg a)
                      (IntAdd b (IntNeg b)))))))
      _ ≈z IntAdd intZero intZero :=
            zring.add_congr (zAdd_neg a) (zAdd_neg b)
      _ ≈z intZero := zZero_add intZero
  exact zring.symm
    (zEq_neg_of_add_eq_zero (a := IntAdd a b)
      (b := IntAdd (IntNeg a) (IntNeg b)) hzero)

private inductive ZExpr where
  | var : Nat -> ZExpr
  | add : ZExpr -> ZExpr -> ZExpr
  | mul : ZExpr -> ZExpr -> ZExpr
  | neg : ZExpr -> ZExpr

private structure ZTerm where
  neg : Bool
  vars : List Nat

private def eSub (a b : ZExpr) : ZExpr :=
  ZExpr.add a (ZExpr.neg b)

private def zMonoEval (vars : Nat -> IntegerUp) : List Nat -> IntegerUp
  | [] => intOne
  | i :: rest => IntMul (vars i) (zMonoEval vars rest)

private def zTermEval (vars : Nat -> IntegerUp) (t : ZTerm) : IntegerUp :=
  if t.neg then IntNeg (zMonoEval vars t.vars) else zMonoEval vars t.vars

private def zExprEval (vars : Nat -> IntegerUp) : ZExpr -> IntegerUp
  | ZExpr.var i => vars i
  | ZExpr.add a b => IntAdd (zExprEval vars a) (zExprEval vars b)
  | ZExpr.mul a b => IntMul (zExprEval vars a) (zExprEval vars b)
  | ZExpr.neg a => IntNeg (zExprEval vars a)

private def zTermNeg (t : ZTerm) : ZTerm :=
  { neg := !t.neg, vars := t.vars }

private def zTermMul (t u : ZTerm) : ZTerm :=
  { neg := if t.neg then !u.neg else u.neg, vars := t.vars ++ u.vars }

private def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natEqBool a b

private def natListEqBool : List Nat -> List Nat -> Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => if natEqBool x y then natListEqBool xs ys else false

private def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLeBool a b

private def natListLeBool (a b : Nat) : Bool :=
  natLeBool a b

private def natInsert (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys => if natListLeBool x y then x :: y :: ys else y :: natInsert x ys

private def natSort : List Nat -> List Nat
  | [] => []
  | x :: xs => natInsert x (natSort xs)

private def zTermCanonical (t : ZTerm) : ZTerm :=
  { neg := t.neg, vars := natSort t.vars }

private def zTermsMulOne (t : ZTerm) : List ZTerm -> List ZTerm
  | [] => []
  | u :: us => zTermMul t u :: zTermsMulOne t us

private def zTermsMul : List ZTerm -> List ZTerm -> List ZTerm
  | [], _ => []
  | t :: ts, us => zTermsMulOne t us ++ zTermsMul ts us

private def zExprTerms : ZExpr -> List ZTerm
  | ZExpr.var i => [{ neg := false, vars := [i] }]
  | ZExpr.add a b => zExprTerms a ++ zExprTerms b
  | ZExpr.mul a b => zTermsMul (zExprTerms a) (zExprTerms b)
  | ZExpr.neg a => List.map zTermNeg (zExprTerms a)

private def natLexLeBool : List Nat -> List Nat -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if natEqBool a b then natLexLeBool as bs else natLeBool a b

private def zTermLeBool (a b : ZTerm) : Bool :=
  if natListEqBool a.vars b.vars then
    match a.neg, b.neg with
    | false, false => true
    | false, true => true
    | true, false => false
    | true, true => true
  else
    natLexLeBool a.vars b.vars

private def zTermInsert (t : ZTerm) : List ZTerm -> List ZTerm
  | [] => [t]
  | u :: us =>
      if zTermLeBool t u then t :: u :: us else u :: zTermInsert t us

private def zTermSort : List ZTerm -> List ZTerm
  | [] => []
  | t :: ts => zTermInsert t (zTermSort ts)

private def zTermOppositeSame (a b : ZTerm) : Bool :=
  match a.neg, b.neg with
  | false, false => false
  | false, true => natListEqBool a.vars b.vars
  | true, false => natListEqBool a.vars b.vars
  | true, true => false

private def zCancelStep : List ZTerm -> ZTerm -> List ZTerm
  | [], t => [t]
  | u :: us, t =>
      if zTermOppositeSame t u then us else t :: u :: us

private def zCancelGo : List ZTerm -> List ZTerm -> List ZTerm
  | acc, [] => acc
  | acc, t :: ts => zCancelGo (zCancelStep acc t) ts

private def zCancelTerms (terms : List ZTerm) : List ZTerm :=
  zTermSort (zCancelGo [] terms)

private def zExprNorm (e : ZExpr) : List ZTerm :=
  zCancelTerms (zTermSort (List.map zTermCanonical (zExprTerms e)))

private def zSumTerms (vars : Nat -> IntegerUp) : List ZTerm -> IntegerUp
  | [] => intZero
  | t :: terms => IntAdd (zTermEval vars t) (zSumTerms vars terms)

private theorem natInsert_perm (x : Nat) :
    ∀ xs : List Nat,
      BEDC.Algebra.FiniteFold.ListPerm (natInsert x xs) (x :: xs)
  | [] => by
      exact BEDC.Algebra.FiniteFold.ListPerm.cons x
        BEDC.Algebra.FiniteFold.ListPerm.nil
  | y :: ys => by
      cases h : natListLeBool x y
      · unfold natInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.ListPerm.trans
          (BEDC.Algebra.FiniteFold.ListPerm.cons y (natInsert_perm x ys))
          (BEDC.Algebra.FiniteFold.ListPerm.swap y x ys)
      · unfold natInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.listPerm_refl (x :: y :: ys)

private theorem natSort_perm :
    ∀ xs : List Nat,
      BEDC.Algebra.FiniteFold.ListPerm (natSort xs) xs
  | [] => BEDC.Algebra.FiniteFold.ListPerm.nil
  | x :: xs =>
      BEDC.Algebra.FiniteFold.ListPerm.trans
        (natInsert_perm x (natSort xs))
        (BEDC.Algebra.FiniteFold.ListPerm.cons x (natSort_perm xs))

private theorem zMonoEval_perm (vars : Nat -> IntegerUp) :
    ∀ {xs ys : List Nat},
      BEDC.Algebra.FiniteFold.ListPerm xs ys ->
        zMonoEval vars xs ≈z zMonoEval vars ys
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.nil =>
      zEq_refl intOne
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.cons x p => by
      exact zring.mul_congr (zEq_refl (vars x)) (zMonoEval_perm vars p)
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.swap x y xs => by
      exact zring.trans (zring.symm (zring.mul_assoc (vars x) (vars y) (zMonoEval vars xs)))
        (zring.trans
          (zring.mul_congr (zring.mul_comm (vars x) (vars y))
            (zEq_refl (zMonoEval vars xs)))
          (zring.mul_assoc (vars y) (vars x) (zMonoEval vars xs)))
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.trans p q =>
      zring.trans (zMonoEval_perm vars p) (zMonoEval_perm vars q)

private theorem zTermCanonical_eval (vars : Nat -> IntegerUp) (t : ZTerm) :
    zTermEval vars (zTermCanonical t) ≈z zTermEval vars t := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact zMonoEval_perm vars (natSort_perm mono)
      · exact zring.neg_congr (zMonoEval_perm vars (natSort_perm mono))

private theorem zSum_canonical (vars : Nat -> IntegerUp) :
    ∀ terms : List ZTerm,
      zSumTerms vars (List.map zTermCanonical terms) ≈z zSumTerms vars terms
  | [] => zEq_refl intZero
  | t :: ts => by
      exact zring.add_congr (zTermCanonical_eval vars t) (zSum_canonical vars ts)

private theorem zTermInsert_perm (t : ZTerm) :
    ∀ terms : List ZTerm,
      BEDC.Algebra.FiniteFold.ListPerm (zTermInsert t terms) (t :: terms)
  | [] => by
      exact BEDC.Algebra.FiniteFold.ListPerm.cons t
        BEDC.Algebra.FiniteFold.ListPerm.nil
  | u :: us => by
      cases h : zTermLeBool t u
      · unfold zTermInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.ListPerm.trans
          (BEDC.Algebra.FiniteFold.ListPerm.cons u (zTermInsert_perm t us))
          (BEDC.Algebra.FiniteFold.ListPerm.swap u t us)
      · unfold zTermInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.listPerm_refl (t :: u :: us)

private theorem zTermSort_perm :
    ∀ terms : List ZTerm,
      BEDC.Algebra.FiniteFold.ListPerm (zTermSort terms) terms
  | [] => BEDC.Algebra.FiniteFold.ListPerm.nil
  | t :: ts =>
      BEDC.Algebra.FiniteFold.ListPerm.trans
        (zTermInsert_perm t (zTermSort ts))
        (BEDC.Algebra.FiniteFold.ListPerm.cons t (zTermSort_perm ts))

private theorem zSum_perm (vars : Nat -> IntegerUp) :
    ∀ {xs ys : List ZTerm},
      BEDC.Algebra.FiniteFold.ListPerm xs ys ->
        zSumTerms vars xs ≈z zSumTerms vars ys
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.nil =>
      zEq_refl intZero
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.cons x p => by
      exact zring.add_congr (zEq_refl (zTermEval vars x)) (zSum_perm vars p)
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.swap x y xs => by
      exact zring.trans
        (zring.symm (zring.add_assoc (zTermEval vars x) (zTermEval vars y)
          (zSumTerms vars xs)))
        (zring.trans
          (zring.add_congr (zring.add_comm (zTermEval vars x) (zTermEval vars y))
            (zEq_refl (zSumTerms vars xs)))
          (zring.add_assoc (zTermEval vars y) (zTermEval vars x)
            (zSumTerms vars xs)))
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.trans p q =>
      zring.trans (zSum_perm vars p) (zSum_perm vars q)

private theorem zSum_sort (vars : Nat -> IntegerUp) (terms : List ZTerm) :
    zSumTerms vars (zTermSort terms) ≈z zSumTerms vars terms := by
  exact zSum_perm vars (zTermSort_perm terms)

private theorem natEqBool_eq_true :
    ∀ a b : Nat, natEqBool a b = true -> a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => by cases h
  | Nat.succ _, 0, h => by cases h
  | Nat.succ a, Nat.succ b, h => by
      exact congrArg Nat.succ (natEqBool_eq_true a b h)

private theorem natListEqBool_eq_true :
    ∀ xs ys : List Nat, natListEqBool xs ys = true -> xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
      unfold natListEqBool at h
      cases heq : natEqBool x y
      · rw [heq] at h
        cases h
      · rw [heq] at h
        have headEq : x = y := natEqBool_eq_true x y heq
        have tailEq : xs = ys := natListEqBool_eq_true xs ys h
        cases headEq
        cases tailEq
        rfl

private theorem zTermOppositeSame_eval_zero
    (vars : Nat -> IntegerUp) (t u : ZTerm) :
    zTermOppositeSame t u = true ->
      IntAdd (zTermEval vars t) (zTermEval vars u) ≈z intZero := by
  intro h
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · cases h
          · unfold zTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change IntAdd (zMonoEval vars uVars) (IntNeg (zMonoEval vars uVars)) ≈z intZero
            exact zAdd_neg (zMonoEval vars uVars)
          · unfold zTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change IntAdd (IntNeg (zMonoEval vars uVars)) (zMonoEval vars uVars) ≈z intZero
            exact zNeg_add (zMonoEval vars uVars)
          · cases h

private theorem zCancelStep_sound (vars : Nat -> IntegerUp) :
    ∀ acc : List ZTerm, ∀ t : ZTerm,
      zSumTerms vars (zCancelStep acc t) ≈z
        IntAdd (zTermEval vars t) (zSumTerms vars acc)
  | [], t => by
      exact zring.refl (IntAdd (zTermEval vars t) intZero)
  | u :: us, t => by
      cases h : zTermOppositeSame t u
      · change zSumTerms vars
          (if zTermOppositeSame t u then us else t :: u :: us) ≈z
          IntAdd (zTermEval vars t) (IntAdd (zTermEval vars u) (zSumTerms vars us))
        rw [h]
        exact zring.refl
          (IntAdd (zTermEval vars t) (IntAdd (zTermEval vars u) (zSumTerms vars us)))
      · change zSumTerms vars
          (if zTermOppositeSame t u then us else t :: u :: us) ≈z
          IntAdd (zTermEval vars t) (IntAdd (zTermEval vars u) (zSumTerms vars us))
        rw [h]
        exact zring.symm
          (zring.trans
            (zring.symm (zring.add_assoc (zTermEval vars t)
              (zTermEval vars u) (zSumTerms vars us)))
            (zring.trans
              (zring.add_congr (zTermOppositeSame_eval_zero vars t u h)
                (zring.refl (zSumTerms vars us)))
              (zring.zero_add (zSumTerms vars us))))

private theorem zCancelGo_sound (vars : Nat -> IntegerUp) :
    ∀ acc terms : List ZTerm,
      zSumTerms vars (zCancelGo acc terms) ≈z
        IntAdd (zSumTerms vars terms) (zSumTerms vars acc)
  | acc, [] => by
      exact zring.symm (zring.zero_add (zSumTerms vars acc))
  | acc, t :: ts => by
      have tail := zCancelGo_sound vars (zCancelStep acc t) ts
      exact zring.trans tail
        (zring.trans
          (zring.add_congr (zring.refl (zSumTerms vars ts))
            (zCancelStep_sound vars acc t))
          (zring.trans
            (zring.symm (zring.add_assoc (zSumTerms vars ts)
              (zTermEval vars t) (zSumTerms vars acc)))
            (zring.add_congr
              (zring.add_comm (zSumTerms vars ts) (zTermEval vars t))
              (zring.refl (zSumTerms vars acc)))))

private theorem zCancelTerms_sound (vars : Nat -> IntegerUp) (terms : List ZTerm) :
    zSumTerms vars (zCancelTerms terms) ≈z zSumTerms vars terms := by
  unfold zCancelTerms
  exact zring.trans (zSum_sort vars (zCancelGo [] terms))
    (zring.trans (zCancelGo_sound vars [] terms)
      (zring.trans
        (zring.add_congr (zring.refl (zSumTerms vars terms))
          (zring.refl intZero))
        (zring.add_zero (zSumTerms vars terms))))

private theorem zSum_append (vars : Nat -> IntegerUp) (xs ys : List ZTerm) :
    zSumTerms vars (xs ++ ys) ≈z IntAdd (zSumTerms vars xs) (zSumTerms vars ys) := by
  induction xs with
  | nil =>
      exact zring.symm (zring.zero_add (zSumTerms vars ys))
  | cons x xs ih =>
      exact zring.trans
        (zring.add_congr (zEq_refl (zTermEval vars x)) ih)
        (zring.symm (zring.add_assoc (zTermEval vars x)
          (zSumTerms vars xs) (zSumTerms vars ys)))

private theorem zMonoEval_append (vars : Nat -> IntegerUp) :
    ∀ xs ys : List Nat,
      zMonoEval vars (xs ++ ys) ≈z IntMul (zMonoEval vars xs) (zMonoEval vars ys)
  | [], ys => by
      exact zring.symm (zring.one_mul (zMonoEval vars ys))
  | x :: xs, ys => by
      exact zring.trans
        (zring.mul_congr (zEq_refl (vars x)) (zMonoEval_append vars xs ys))
        (zring.symm (zring.mul_assoc (vars x) (zMonoEval vars xs)
          (zMonoEval vars ys)))

private theorem zTermEval_neg (vars : Nat -> IntegerUp) (t : ZTerm) :
    zTermEval vars (zTermNeg t) ≈z IntNeg (zTermEval vars t) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact zEq_refl (IntNeg (zMonoEval vars mono))
      · exact zring.symm (zNeg_neg (zMonoEval vars mono))

private theorem zTermEval_mul (vars : Nat -> IntegerUp) (t u : ZTerm) :
    zTermEval vars (zTermMul t u) ≈z
      IntMul (zTermEval vars t) (zTermEval vars u) := by
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · exact zMonoEval_append vars tVars uVars
          · exact zring.trans
              (zring.neg_congr (zMonoEval_append vars tVars uVars))
              (zring.symm (zring.mul_neg (zMonoEval vars tVars)
                (zMonoEval vars uVars)))
          · exact zring.trans
              (zring.neg_congr (zMonoEval_append vars tVars uVars))
              (zring.symm (zring.neg_mul (zMonoEval vars tVars)
                (zMonoEval vars uVars)))
          · exact zring.trans (zMonoEval_append vars tVars uVars)
              (zring.symm (zring.neg_neg_mul_neg (zMonoEval vars tVars)
                (zMonoEval vars uVars)))

private theorem zSum_neg (vars : Nat -> IntegerUp) :
    ∀ terms : List ZTerm,
      zSumTerms vars (List.map zTermNeg terms) ≈z IntNeg (zSumTerms vars terms)
  | [] => by
      exact zring.symm zNeg_zero
  | t :: ts => by
      exact zring.trans
        (zring.add_congr (zTermEval_neg vars t) (zSum_neg vars ts))
        (zring.symm (zNeg_add_pair (zTermEval vars t) (zSumTerms vars ts)))

private theorem zTermsMulOne_sound (vars : Nat -> IntegerUp) (t : ZTerm) :
    ∀ terms : List ZTerm,
      zSumTerms vars (zTermsMulOne t terms) ≈z
        IntMul (zTermEval vars t) (zSumTerms vars terms)
  | [] => by
      exact zring.symm (zring.mul_zero (zTermEval vars t))
  | u :: us => by
      exact zring.trans
        (zring.add_congr (zTermEval_mul vars t u) (zTermsMulOne_sound vars t us))
        (zring.symm (zring.left_distrib (zTermEval vars t)
          (zTermEval vars u) (zSumTerms vars us)))

private theorem zTermsMul_sound (vars : Nat -> IntegerUp) :
    ∀ xs ys : List ZTerm,
      zSumTerms vars (zTermsMul xs ys) ≈z
        IntMul (zSumTerms vars xs) (zSumTerms vars ys)
  | [], ys => by
      exact zring.symm (zring.zero_mul (zSumTerms vars ys))
  | x :: xs, ys => by
      exact zring.trans
        (zSum_append vars (zTermsMulOne x ys) (zTermsMul xs ys))
        (zring.trans
          (zring.add_congr (zTermsMulOne_sound vars x ys)
            (zTermsMul_sound vars xs ys))
          (zring.symm (zring.right_distrib (zTermEval vars x)
            (zSumTerms vars xs) (zSumTerms vars ys))))

private theorem zExprTerms_sound_var (vars : Nat -> IntegerUp) (i : Nat) :
    zExprEval vars (ZExpr.var i) ≈z zSumTerms vars (zExprTerms (ZExpr.var i)) := by
  change vars i ≈z IntAdd (IntMul (vars i) intOne) intZero
  exact zring.symm
    (zring.trans (zring.add_zero (IntMul (vars i) intOne))
      (zMul_one (vars i)))

private theorem zExprTerms_sound :
    ∀ (vars : Nat -> IntegerUp) (e : ZExpr),
      zExprEval vars e ≈z zSumTerms vars (zExprTerms e)
  | vars, ZExpr.var i =>
      zExprTerms_sound_var vars i
  | vars, ZExpr.add a b => by
      exact zring.trans
        (zring.add_congr (zExprTerms_sound vars a) (zExprTerms_sound vars b))
        (zring.symm (zSum_append vars (zExprTerms a) (zExprTerms b)))
  | vars, ZExpr.mul a b => by
      exact zring.trans
        (zring.mul_congr (zExprTerms_sound vars a) (zExprTerms_sound vars b))
        (zring.symm (zTermsMul_sound vars (zExprTerms a) (zExprTerms b)))
  | vars, ZExpr.neg a => by
      exact zring.trans (zring.neg_congr (zExprTerms_sound vars a))
        (zring.symm (zSum_neg vars (zExprTerms a)))

private theorem zExprNorm_sound (vars : Nat -> IntegerUp) (e : ZExpr) :
    zExprEval vars e ≈z zSumTerms vars (zExprNorm e) := by
  exact zring.trans (zExprTerms_sound vars e)
    (zring.trans
      (zring.symm (zSum_canonical vars (zExprTerms e)))
      (zring.trans
        (zring.symm (zSum_sort vars (List.map zTermCanonical (zExprTerms e))))
        (zring.symm
          (zCancelTerms_sound vars
            (zTermSort (List.map zTermCanonical (zExprTerms e)))))))

private theorem zExpr_same_norm (vars : Nat -> IntegerUp) (a b : ZExpr)
    (h : zExprNorm a = zExprNorm b) :
    zExprEval vars a ≈z zExprEval vars b := by
  have left := zExprNorm_sound vars a
  have right := zExprNorm_sound vars b
  rw [h] at left
  exact zring.trans left (zring.symm right)

private structure QuatExpr where
  re : ZExpr
  imI : ZExpr
  imJ : ZExpr
  imK : ZExpr

private def qExprX : QuatExpr :=
  { re := ZExpr.var 0, imI := ZExpr.var 1, imJ := ZExpr.var 2, imK := ZExpr.var 3 }

private def qExprY : QuatExpr :=
  { re := ZExpr.var 4, imI := ZExpr.var 5, imJ := ZExpr.var 6, imK := ZExpr.var 7 }

private def qExprZ : QuatExpr :=
  { re := ZExpr.var 8, imI := ZExpr.var 9, imJ := ZExpr.var 10, imK := ZExpr.var 11 }

private def qExprAdd (x y : QuatExpr) : QuatExpr :=
  { re := ZExpr.add x.re y.re
    imI := ZExpr.add x.imI y.imI
    imJ := ZExpr.add x.imJ y.imJ
    imK := ZExpr.add x.imK y.imK }

private def qExprMul (x y : QuatExpr) : QuatExpr :=
  { re := eSub (eSub (eSub (ZExpr.mul x.re y.re) (ZExpr.mul x.imI y.imI))
      (ZExpr.mul x.imJ y.imJ)) (ZExpr.mul x.imK y.imK)
    imI := ZExpr.add (ZExpr.add (ZExpr.mul x.re y.imI) (ZExpr.mul x.imI y.re))
      (eSub (ZExpr.mul x.imJ y.imK) (ZExpr.mul x.imK y.imJ))
    imJ := ZExpr.add (eSub (ZExpr.mul x.re y.imJ) (ZExpr.mul x.imI y.imK))
      (ZExpr.add (ZExpr.mul x.imJ y.re) (ZExpr.mul x.imK y.imI))
    imK := ZExpr.add (ZExpr.add (ZExpr.mul x.re y.imK) (ZExpr.mul x.imI y.imJ))
      (eSub (ZExpr.mul x.imK y.re) (ZExpr.mul x.imJ y.imI)) }

private def qExprNorm (x : QuatExpr) : ZExpr :=
  ZExpr.add (ZExpr.add (ZExpr.mul x.re x.re) (ZExpr.mul x.imI x.imI))
    (ZExpr.add (ZExpr.mul x.imJ x.imJ) (ZExpr.mul x.imK x.imK))

private def quatExprVars (x y z : Quat) : Nat -> IntegerUp
  | 0 => x.re
  | 1 => x.imI
  | 2 => x.imJ
  | 3 => x.imK
  | 4 => y.re
  | 5 => y.imI
  | 6 => y.imJ
  | 7 => y.imK
  | 8 => z.re
  | 9 => z.imI
  | 10 => z.imJ
  | 11 => z.imK
  | _ => intZero

theorem quatNorm_mul (x y : Quat) :
    quatNorm (quatMul x y) ≈z IntMul (quatNorm x) (quatNorm y) := by
  let vars := quatExprVars x y quatZero
  change zExprEval vars (qExprNorm (qExprMul qExprX qExprY)) ≈z
    zExprEval vars (ZExpr.mul (qExprNorm qExprX) (qExprNorm qExprY))
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_assoc_re (x y z : Quat) :
    (quatMul (quatMul x y) z).re ≈z (quatMul x (quatMul y z)).re := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprMul qExprX qExprY) qExprZ).re ≈z
    zExprEval vars (qExprMul qExprX (qExprMul qExprY qExprZ)).re
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_assoc_imI (x y z : Quat) :
    (quatMul (quatMul x y) z).imI ≈z (quatMul x (quatMul y z)).imI := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprMul qExprX qExprY) qExprZ).imI ≈z
    zExprEval vars (qExprMul qExprX (qExprMul qExprY qExprZ)).imI
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_assoc_imJ (x y z : Quat) :
    (quatMul (quatMul x y) z).imJ ≈z (quatMul x (quatMul y z)).imJ := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprMul qExprX qExprY) qExprZ).imJ ≈z
    zExprEval vars (qExprMul qExprX (qExprMul qExprY qExprZ)).imJ
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_assoc_imK (x y z : Quat) :
    (quatMul (quatMul x y) z).imK ≈z (quatMul x (quatMul y z)).imK := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprMul qExprX qExprY) qExprZ).imK ≈z
    zExprEval vars (qExprMul qExprX (qExprMul qExprY qExprZ)).imK
  exact zExpr_same_norm vars _ _ rfl

theorem quatMul_assoc (x y z : Quat) :
    QuatEq (quatMul (quatMul x y) z) (quatMul x (quatMul y z)) := by
  exact ⟨quatMul_assoc_re x y z, quatMul_assoc_imI x y z,
    quatMul_assoc_imJ x y z, quatMul_assoc_imK x y z⟩

private theorem quatMul_add_distrib_re (x y z : Quat) :
    (quatMul x (quatAdd y z)).re ≈z
      (quatAdd (quatMul x y) (quatMul x z)).re := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul qExprX (qExprAdd qExprY qExprZ)).re ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprY) (qExprMul qExprX qExprZ)).re
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_add_distrib_imI (x y z : Quat) :
    (quatMul x (quatAdd y z)).imI ≈z
      (quatAdd (quatMul x y) (quatMul x z)).imI := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul qExprX (qExprAdd qExprY qExprZ)).imI ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprY) (qExprMul qExprX qExprZ)).imI
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_add_distrib_imJ (x y z : Quat) :
    (quatMul x (quatAdd y z)).imJ ≈z
      (quatAdd (quatMul x y) (quatMul x z)).imJ := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul qExprX (qExprAdd qExprY qExprZ)).imJ ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprY) (qExprMul qExprX qExprZ)).imJ
  exact zExpr_same_norm vars _ _ rfl

private theorem quatMul_add_distrib_imK (x y z : Quat) :
    (quatMul x (quatAdd y z)).imK ≈z
      (quatAdd (quatMul x y) (quatMul x z)).imK := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul qExprX (qExprAdd qExprY qExprZ)).imK ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprY) (qExprMul qExprX qExprZ)).imK
  exact zExpr_same_norm vars _ _ rfl

theorem quatMul_add_distrib (x y z : Quat) :
    QuatEq (quatMul x (quatAdd y z))
      (quatAdd (quatMul x y) (quatMul x z)) := by
  exact ⟨quatMul_add_distrib_re x y z, quatMul_add_distrib_imI x y z,
    quatMul_add_distrib_imJ x y z, quatMul_add_distrib_imK x y z⟩

private theorem quatAdd_mul_distrib_re (x y z : Quat) :
    (quatMul (quatAdd x y) z).re ≈z
      (quatAdd (quatMul x z) (quatMul y z)).re := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprAdd qExprX qExprY) qExprZ).re ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprZ) (qExprMul qExprY qExprZ)).re
  exact zExpr_same_norm vars _ _ rfl

private theorem quatAdd_mul_distrib_imI (x y z : Quat) :
    (quatMul (quatAdd x y) z).imI ≈z
      (quatAdd (quatMul x z) (quatMul y z)).imI := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprAdd qExprX qExprY) qExprZ).imI ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprZ) (qExprMul qExprY qExprZ)).imI
  exact zExpr_same_norm vars _ _ rfl

private theorem quatAdd_mul_distrib_imJ (x y z : Quat) :
    (quatMul (quatAdd x y) z).imJ ≈z
      (quatAdd (quatMul x z) (quatMul y z)).imJ := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprAdd qExprX qExprY) qExprZ).imJ ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprZ) (qExprMul qExprY qExprZ)).imJ
  exact zExpr_same_norm vars _ _ rfl

private theorem quatAdd_mul_distrib_imK (x y z : Quat) :
    (quatMul (quatAdd x y) z).imK ≈z
      (quatAdd (quatMul x z) (quatMul y z)).imK := by
  let vars := quatExprVars x y z
  change zExprEval vars (qExprMul (qExprAdd qExprX qExprY) qExprZ).imK ≈z
    zExprEval vars (qExprAdd (qExprMul qExprX qExprZ) (qExprMul qExprY qExprZ)).imK
  exact zExpr_same_norm vars _ _ rfl

theorem quatAdd_mul_distrib (x y z : Quat) :
    QuatEq (quatMul (quatAdd x y) z)
      (quatAdd (quatMul x z) (quatMul y z)) := by
  exact ⟨quatAdd_mul_distrib_re x y z, quatAdd_mul_distrib_imI x y z,
    quatAdd_mul_distrib_imJ x y z, quatAdd_mul_distrib_imK x y z⟩

structure QuaternionBasicLaws where
  eq_refl : ∀ x : Quat, QuatEq x x
  eq_symm : ∀ {x y : Quat}, QuatEq x y -> QuatEq y x
  eq_trans : ∀ {x y z : Quat}, QuatEq x y -> QuatEq y z -> QuatEq x z
  add_respects :
    ∀ {x x' y y' : Quat}, QuatEq x x' -> QuatEq y y' ->
      QuatEq (quatAdd x y) (quatAdd x' y')
  neg_respects : ∀ {x y : Quat}, QuatEq x y -> QuatEq (quatNeg x) (quatNeg y)
  mul_respects :
    ∀ {x x' y y' : Quat}, QuatEq x x' -> QuatEq y y' ->
      QuatEq (quatMul x y) (quatMul x' y')
  add_comm : ∀ x y : Quat, QuatEq (quatAdd x y) (quatAdd y x)
  add_assoc :
    ∀ x y z : Quat, QuatEq (quatAdd (quatAdd x y) z) (quatAdd x (quatAdd y z))
  add_zero : ∀ x : Quat, QuatEq (quatAdd x quatZero) x
  zero_add : ∀ x : Quat, QuatEq (quatAdd quatZero x) x
  add_neg : ∀ x : Quat, QuatEq (quatAdd x (quatNeg x)) quatZero
  neg_add : ∀ x : Quat, QuatEq (quatAdd (quatNeg x) x) quatZero
  mul_one : ∀ x : Quat, QuatEq (quatMul x quatOne) x
  one_mul : ∀ x : Quat, QuatEq (quatMul quatOne x) x
  mul_zero : ∀ x : Quat, QuatEq (quatMul x quatZero) quatZero
  zero_mul : ∀ x : Quat, QuatEq (quatMul quatZero x) quatZero
  mul_assoc :
    ∀ x y z : Quat, QuatEq (quatMul (quatMul x y) z) (quatMul x (quatMul y z))
  left_distrib :
    ∀ x y z : Quat,
      QuatEq (quatMul x (quatAdd y z))
        (quatAdd (quatMul x y) (quatMul x z))
  right_distrib :
    ∀ x y z : Quat,
      QuatEq (quatMul (quatAdd x y) z)
        (quatAdd (quatMul x z) (quatMul y z))

def quaternion_basic_laws : QuaternionBasicLaws where
  eq_refl := QuatEq_refl
  eq_symm := by
    intro x y
    exact QuatEq_symm
  eq_trans := by
    intro x y z
    exact QuatEq_trans
  add_respects := by
    intro x x' y y'
    exact quatAdd_respects
  neg_respects := by
    intro x y
    exact quatNeg_respects
  mul_respects := by
    intro x x' y y'
    exact quatMul_respects
  add_comm := quatAdd_comm
  add_assoc := quatAdd_assoc
  add_zero := quatAdd_zero
  zero_add := quatZero_add
  add_neg := quatAdd_neg
  neg_add := quatNeg_add
  mul_one := quatMul_one
  one_mul := quatOne_mul
  mul_zero := quatMul_zero
  zero_mul := quatZero_mul
  mul_assoc := quatMul_assoc
  left_distrib := quatMul_add_distrib
  right_distrib := quatAdd_mul_distrib

instance QuaternionUp_RelEquiv :
    BEDC.Algebra.Rel.RelEquiv Quat where
  rel := QuatEq
  refl := QuatEq_refl
  symm := by
    intro x y
    exact QuatEq_symm
  trans := by
    intro x y z
    exact QuatEq_trans

instance QuaternionUp_RelRing :
    BEDC.Algebra.Rel.RelRing Quat QuatEq where
  zero := quatZero
  one := quatOne
  add := quatAdd
  mul := quatMul
  neg := quatNeg
  refl := quaternion_basic_laws.eq_refl
  symm := by
    intro x y
    exact quaternion_basic_laws.eq_symm
  trans := by
    intro x y z
    exact quaternion_basic_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact quaternion_basic_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact quaternion_basic_laws.mul_respects
  neg_congr := by
    intro x y
    exact quaternion_basic_laws.neg_respects
  add_assoc := quaternion_basic_laws.add_assoc
  add_comm := quaternion_basic_laws.add_comm
  add_zero := quaternion_basic_laws.add_zero
  zero_add := quaternion_basic_laws.zero_add
  add_neg := quaternion_basic_laws.add_neg
  neg_add := quaternion_basic_laws.neg_add
  mul_assoc := quaternion_basic_laws.mul_assoc
  mul_one := quaternion_basic_laws.mul_one
  one_mul := quaternion_basic_laws.one_mul
  mul_zero := quaternion_basic_laws.mul_zero
  zero_mul := quaternion_basic_laws.zero_mul
  left_distrib := quaternion_basic_laws.left_distrib
  right_distrib := quaternion_basic_laws.right_distrib

end BEDC.Derived.QuaternionUp
