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

end BEDC.Derived.QuaternionUp
