namespace BEDC.Algebra.Rel

class RelEquiv (A : Type u) where
  rel : A -> A -> Prop
  refl : ∀ x : A, rel x x
  symm : ∀ {x y : A}, rel x y -> rel y x
  trans : ∀ {x y z : A}, rel x y -> rel y z -> rel x z

class RelRing (A : Type u) (r : A -> A -> Prop) where
  zero : A
  one : A
  add : A -> A -> A
  mul : A -> A -> A
  neg : A -> A
  refl : ∀ x : A, r x x
  symm : ∀ {x y : A}, r x y -> r y x
  trans : ∀ {x y z : A}, r x y -> r y z -> r x z
  add_congr : ∀ {x x' y y' : A}, r x x' -> r y y' -> r (add x y) (add x' y')
  mul_congr : ∀ {x x' y y' : A}, r x x' -> r y y' -> r (mul x y) (mul x' y')
  neg_congr : ∀ {x y : A}, r x y -> r (neg x) (neg y)
  add_assoc : ∀ x y z : A, r (add (add x y) z) (add x (add y z))
  add_comm : ∀ x y : A, r (add x y) (add y x)
  add_zero : ∀ x : A, r (add x zero) x
  zero_add : ∀ x : A, r (add zero x) x
  add_neg : ∀ x : A, r (add x (neg x)) zero
  neg_add : ∀ x : A, r (add (neg x) x) zero
  mul_assoc : ∀ x y z : A, r (mul (mul x y) z) (mul x (mul y z))
  mul_one : ∀ x : A, r (mul x one) x
  one_mul : ∀ x : A, r (mul one x) x
  mul_zero : ∀ x : A, r (mul x zero) zero
  zero_mul : ∀ x : A, r (mul zero x) zero
  left_distrib : ∀ x y z : A, r (mul x (add y z)) (add (mul x y) (mul x z))
  right_distrib : ∀ x y z : A, r (mul (add x y) z) (add (mul x z) (mul y z))

class RelCommRing (A : Type u) (r : A -> A -> Prop) extends RelRing A r where
  mul_comm : ∀ x y : A, r (mul x y) (mul y x)

namespace RelRing

variable {A : Type u} {r : A -> A -> Prop} (R : RelRing A r)

def sub (x y : A) : A :=
  R.add x (R.neg y)

theorem sub_eq_add_neg (x y : A) :
    r (R.sub x y) (R.add x (R.neg y)) :=
  R.refl (R.add x (R.neg y))

theorem add_right_congr {x y : A} (h : r x y) (z : A) :
    r (R.add x z) (R.add y z) :=
  R.add_congr h (R.refl z)

theorem add_left_congr (z : A) {x y : A} (h : r x y) :
    r (R.add z x) (R.add z y) :=
  R.add_congr (R.refl z) h

theorem mul_right_congr {x y : A} (h : r x y) (z : A) :
    r (R.mul x z) (R.mul y z) :=
  R.mul_congr h (R.refl z)

theorem mul_left_congr (z : A) {x y : A} (h : r x y) :
    r (R.mul z x) (R.mul z y) :=
  R.mul_congr (R.refl z) h

theorem eq_neg_of_add_eq_zero {a b : A} :
    r (R.add a b) R.zero -> r b (R.neg a) := by
  intro h
  exact R.trans (R.symm (R.zero_add b))
    (R.trans (R.add_right_congr (R.symm (R.neg_add a)) b)
      (R.trans (R.add_assoc (R.neg a) a b)
        (R.trans (R.add_left_congr (R.neg a) h)
          (R.add_zero (R.neg a)))))

theorem neg_neg (a : A) :
    r (R.neg (R.neg a)) a :=
  R.symm (R.eq_neg_of_add_eq_zero (a := R.neg a) (b := a) (R.neg_add a))

theorem neg_zero :
    r (R.neg R.zero) R.zero := by
  exact R.trans (R.symm (R.zero_add (R.neg R.zero)))
    (R.trans (R.add_comm R.zero (R.neg R.zero))
      (R.neg_add R.zero))

theorem neg_eq_of_add_eq_zero {a b : A} :
    r (R.add a b) R.zero -> r (R.neg a) b := by
  intro h
  exact R.symm (R.eq_neg_of_add_eq_zero h)

theorem neg_mul (a b : A) :
    r (R.mul (R.neg a) b) (R.neg (R.mul a b)) := by
  have hzero :
      r (R.add (R.mul a b) (R.mul (R.neg a) b)) R.zero := by
    exact R.trans (R.symm (R.right_distrib a (R.neg a) b))
      (R.trans (R.mul_right_congr (R.add_neg a) b)
        (R.zero_mul b))
  exact R.eq_neg_of_add_eq_zero (a := R.mul a b) (b := R.mul (R.neg a) b) hzero

theorem mul_neg (a b : A) :
    r (R.mul a (R.neg b)) (R.neg (R.mul a b)) := by
  have hzero :
      r (R.add (R.mul a b) (R.mul a (R.neg b))) R.zero := by
    exact R.trans (R.symm (R.left_distrib a b (R.neg b)))
      (R.trans (R.mul_left_congr a (R.add_neg b))
        (R.mul_zero a))
  exact R.eq_neg_of_add_eq_zero (a := R.mul a b) (b := R.mul a (R.neg b)) hzero

theorem neg_neg_mul_neg (a b : A) :
    r (R.mul (R.neg a) (R.neg b)) (R.mul a b) := by
  exact R.trans (R.neg_mul a (R.neg b))
    (R.trans (R.neg_congr (R.mul_neg a b))
      (R.neg_neg (R.mul a b)))

end RelRing

namespace RelCommRing

variable {A : Type u} {r : A -> A -> Prop} (R : RelCommRing A r)

def sub (x y : A) : A :=
  R.toRelRing.sub x y

theorem sub_eq_add_neg (x y : A) :
    r (R.sub x y) (R.add x (R.neg y)) :=
  R.toRelRing.sub_eq_add_neg x y

theorem add_right_congr {x y : A} (h : r x y) (z : A) :
    r (R.add x z) (R.add y z) :=
  R.toRelRing.add_right_congr h z

theorem add_left_congr (z : A) {x y : A} (h : r x y) :
    r (R.add z x) (R.add z y) :=
  R.toRelRing.add_left_congr z h

theorem mul_right_congr {x y : A} (h : r x y) (z : A) :
    r (R.mul x z) (R.mul y z) :=
  R.toRelRing.mul_right_congr h z

theorem mul_left_congr (z : A) {x y : A} (h : r x y) :
    r (R.mul z x) (R.mul z y) :=
  R.toRelRing.mul_left_congr z h

theorem eq_neg_of_add_eq_zero {a b : A} :
    r (R.add a b) R.zero -> r b (R.neg a) :=
  R.toRelRing.eq_neg_of_add_eq_zero

theorem neg_neg (a : A) :
    r (R.neg (R.neg a)) a :=
  R.toRelRing.neg_neg a

theorem neg_zero :
    r (R.neg R.zero) R.zero :=
  R.toRelRing.neg_zero

theorem neg_eq_of_add_eq_zero {a b : A} :
    r (R.add a b) R.zero -> r (R.neg a) b :=
  R.toRelRing.neg_eq_of_add_eq_zero

theorem neg_mul (a b : A) :
    r (R.mul (R.neg a) b) (R.neg (R.mul a b)) :=
  R.toRelRing.neg_mul a b

theorem mul_neg (a b : A) :
    r (R.mul a (R.neg b)) (R.neg (R.mul a b)) :=
  R.toRelRing.mul_neg a b

theorem neg_neg_mul_neg (a b : A) :
    r (R.mul (R.neg a) (R.neg b)) (R.mul a b) :=
  R.toRelRing.neg_neg_mul_neg a b

theorem mul_neg_commuted (a b : A) :
    r (R.mul (R.neg a) b) (R.mul a (R.neg b)) := by
  exact R.trans (R.neg_mul a b)
    (R.symm (R.mul_neg a b))

end RelCommRing

theorem sub_eq_add_neg {A : Type u} {r : A -> A -> Prop}
    (R : RelRing A r) (x y : A) :
    r (R.sub x y) (R.add x (R.neg y)) :=
  R.sub_eq_add_neg x y

theorem neg_mul {A : Type u} {r : A -> A -> Prop}
    (R : RelRing A r) (a b : A) :
    r (R.mul (R.neg a) b) (R.neg (R.mul a b)) :=
  R.neg_mul a b

theorem mul_neg {A : Type u} {r : A -> A -> Prop}
    (R : RelRing A r) (a b : A) :
    r (R.mul a (R.neg b)) (R.neg (R.mul a b)) :=
  R.mul_neg a b

theorem neg_neg {A : Type u} {r : A -> A -> Prop}
    (R : RelRing A r) (a : A) :
    r (R.neg (R.neg a)) a :=
  R.neg_neg a

end BEDC.Algebra.Rel
