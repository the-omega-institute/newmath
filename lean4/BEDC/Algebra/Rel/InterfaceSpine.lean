import BEDC.Algebra.Rel.Basic

namespace BEDC.Algebra.Rel

universe u v

class MagmaUp (A : Type u) (E : RelEquiv A) where
  op : A -> A -> A
  op_congr :
    ∀ {x x' y y' : A}, E.rel x x' -> E.rel y y' -> E.rel (op x y) (op x' y')

class SemigroupUp (A : Type u) (E : RelEquiv A) extends MagmaUp A E where
  assoc : ∀ x y z : A, E.rel (op (op x y) z) (op x (op y z))

class MonoidUp (A : Type u) (E : RelEquiv A) extends SemigroupUp A E where
  one : A
  one_mul : ∀ x : A, E.rel (op one x) x
  mul_one : ∀ x : A, E.rel (op x one) x

class GroupUp (A : Type u) (E : RelEquiv A) extends MonoidUp A E where
  inv : A -> A
  inv_congr : ∀ {x y : A}, E.rel x y -> E.rel (inv x) (inv y)
  mul_left_inv : ∀ x : A, E.rel (op (inv x) x) one

class AbGroupUp (A : Type u) (E : RelEquiv A) extends GroupUp A E where
  comm : ∀ x y : A, E.rel (op x y) (op y x)

namespace SemigroupUp

variable {A : Type u} {E : RelEquiv A} (S : SemigroupUp A E)

theorem fourfold_rebracket (a b c d : A) :
    E.rel (S.op (S.op (S.op a b) c) d)
      (S.op a (S.op b (S.op c d))) :=
  E.trans (S.assoc (S.op a b) c d) (S.assoc a b (S.op c d))

end SemigroupUp

namespace MonoidUp

variable {A : Type u} {E : RelEquiv A} (M : MonoidUp A E)

theorem unit_unique (u : A)
    (hleft : ∀ x : A, E.rel (M.op u x) x)
    (_hright : ∀ x : A, E.rel (M.op x u) x) :
    E.rel u M.one :=
  E.trans (E.symm (M.mul_one u)) (hleft M.one)

theorem units_unique (u v : A)
    (hu_left : ∀ x : A, E.rel (M.op u x) x)
    (hv_right : ∀ x : A, E.rel (M.op x v) x) :
    E.rel u v :=
  E.trans (E.symm (hv_right u)) (hu_left v)

end MonoidUp

namespace GroupUp

variable {A : Type u} {E : RelEquiv A} (G : GroupUp A E)

theorem mul_right_inv (a : A) :
    E.rel (G.op a (G.inv a)) G.one := by
  have hinvinv : E.rel (G.inv (G.inv a)) a := by
    exact E.trans (E.symm (G.mul_one (G.inv (G.inv a))))
      (E.trans
        (G.op_congr (E.refl (G.inv (G.inv a)))
          (E.symm (G.mul_left_inv a)))
        (E.trans (E.symm (G.assoc (G.inv (G.inv a)) (G.inv a) a))
          (E.trans
            (G.op_congr (G.mul_left_inv (G.inv a)) (E.refl a))
            (G.one_mul a))))
  exact E.trans
    (E.symm (G.op_congr hinvinv (E.refl (G.inv a))))
    (G.mul_left_inv (G.inv a))

theorem mul_left_cancel {a x y : A}
    (h : E.rel (G.op a x) (G.op a y)) :
    E.rel x y :=
  E.trans (E.symm (G.one_mul x))
    (E.trans
      (G.op_congr (E.symm (G.mul_left_inv a)) (E.refl x))
      (E.trans (G.assoc (G.inv a) a x)
        (E.trans
          (G.op_congr (E.refl (G.inv a)) h)
          (E.trans (E.symm (G.assoc (G.inv a) a y))
            (E.trans
              (G.op_congr (G.mul_left_inv a) (E.refl y))
              (G.one_mul y))))))

theorem mul_right_cancel {a x y : A}
    (h : E.rel (G.op x a) (G.op y a)) :
    E.rel x y :=
  E.trans (E.symm (G.mul_one x))
    (E.trans
      (G.op_congr (E.refl x) (E.symm (G.mul_right_inv a)))
      (E.trans (E.symm (G.assoc x a (G.inv a)))
        (E.trans
          (G.op_congr h (E.refl (G.inv a)))
          (E.trans (G.assoc y a (G.inv a))
            (E.trans
              (G.op_congr (E.refl y) (G.mul_right_inv a))
              (G.mul_one y))))))

end GroupUp

class RingUp (A : Type u) (E : RelEquiv A) where
  add : AbGroupUp A E
  mul : MonoidUp A E
  left_distrib :
    ∀ x y z : A,
      E.rel (mul.op x (add.op y z))
        (add.op (mul.op x y) (mul.op x z))
  right_distrib :
    ∀ x y z : A,
      E.rel (mul.op (add.op x y) z)
        (add.op (mul.op x z) (mul.op y z))

namespace RingUp

variable {A : Type u} {E : RelEquiv A} (R : RingUp A E)

def zero : A :=
  R.add.one

def one : A :=
  R.mul.one

def neg (x : A) : A :=
  R.add.inv x

def addOp (x y : A) : A :=
  R.add.op x y

def mulOp (x y : A) : A :=
  R.mul.op x y

theorem left_zero_absorption (x : A) :
    E.rel (R.mul.op R.zero x) R.zero := by
  let a := R.mul.op R.zero x
  have hleft :
      E.rel (R.mul.op (R.add.op R.zero R.zero) x) a :=
    R.mul.op_congr (R.add.one_mul R.zero) (E.refl x)
  have hidem : E.rel (R.add.op a a) a :=
    E.trans (E.symm (R.right_distrib R.zero R.zero x)) hleft
  exact GroupUp.mul_left_cancel R.add.toGroupUp
    (E.trans hidem (E.symm (R.add.mul_one a)))

theorem right_zero_absorption (x : A) :
    E.rel (R.mul.op x R.zero) R.zero := by
  let a := R.mul.op x R.zero
  have hright :
      E.rel (R.mul.op x (R.add.op R.zero R.zero)) a :=
    R.mul.op_congr (E.refl x) (R.add.one_mul R.zero)
  have hidem : E.rel (R.add.op a a) a :=
    E.trans (E.symm (R.left_distrib x R.zero R.zero)) hright
  exact GroupUp.mul_left_cancel R.add.toGroupUp
    (E.trans hidem (E.symm (R.add.mul_one a)))

def toRelRing : RelRing A E.rel where
  zero := R.zero
  one := R.one
  add := R.add.op
  mul := R.mul.op
  neg := R.neg
  refl := E.refl
  symm := by
    intro x y
    exact E.symm
  trans := by
    intro x y z
    exact E.trans
  add_congr := R.add.op_congr
  mul_congr := R.mul.op_congr
  neg_congr := R.add.inv_congr
  add_assoc := R.add.assoc
  add_comm := R.add.comm
  add_zero := R.add.mul_one
  zero_add := R.add.one_mul
  add_neg := GroupUp.mul_right_inv R.add.toGroupUp
  neg_add := R.add.mul_left_inv
  mul_assoc := R.mul.assoc
  mul_one := R.mul.mul_one
  one_mul := R.mul.one_mul
  mul_zero := R.right_zero_absorption
  zero_mul := R.left_zero_absorption
  left_distrib := R.left_distrib
  right_distrib := R.right_distrib

end RingUp

class CommRingUp (A : Type u) (E : RelEquiv A) extends RingUp A E where
  mul_comm : ∀ x y : A, E.rel (mul.op x y) (mul.op y x)

namespace CommRingUp

variable {A : Type u} {E : RelEquiv A}

theorem right_distrib_of_left
    (add : AbGroupUp A E) (mul : MonoidUp A E)
    (left_distrib :
      ∀ x y z : A,
        E.rel (mul.op x (add.op y z))
          (add.op (mul.op x y) (mul.op x z)))
    (mul_comm : ∀ x y : A, E.rel (mul.op x y) (mul.op y x))
    (x y z : A) :
    E.rel (mul.op (add.op x y) z)
      (add.op (mul.op x z) (mul.op y z)) :=
  E.trans (mul_comm (add.op x y) z)
    (E.trans (left_distrib z x y)
      (add.op_congr (mul_comm z x) (mul_comm z y)))

def ofLeftDistrib
    (add : AbGroupUp A E) (mul : MonoidUp A E)
    (left_distrib :
      ∀ x y z : A,
        E.rel (mul.op x (add.op y z))
          (add.op (mul.op x y) (mul.op x z)))
    (mul_comm : ∀ x y : A, E.rel (mul.op x y) (mul.op y x)) :
    CommRingUp A E where
  add := add
  mul := mul
  left_distrib := left_distrib
  right_distrib := right_distrib_of_left add mul left_distrib mul_comm
  mul_comm := mul_comm

variable (C : CommRingUp A E)

def toRelCommRing : RelCommRing A E.rel :=
  RelCommRing.mk (toRelRing := C.toRingUp.toRelRing) C.mul_comm

end CommRingUp

class FieldUp (A : Type u) (E : RelEquiv A) extends CommRingUp A E where
  apart : A -> A -> Prop
  apart_symm : ∀ {x y : A}, apart x y -> apart y x
  apart_congr :
    ∀ {x x' y y' : A}, E.rel x x' -> E.rel y y' -> apart x y -> apart x' y'
  inv : A -> A
  inv_congr : ∀ {x y : A}, E.rel x y -> E.rel (inv x) (inv y)
  mul_inv :
    ∀ x : A, apart x add.one -> E.rel (mul.op x (inv x)) mul.one

class ModuleUp
    (RCarrier : Type u) (RE : RelEquiv RCarrier)
    (MCarrier : Type v) (ME : RelEquiv MCarrier)
    (R : RingUp RCarrier RE) (M : AbGroupUp MCarrier ME) where
  smul : RCarrier -> MCarrier -> MCarrier
  smul_congr :
    ∀ {a b : RCarrier} {x y : MCarrier},
      RE.rel a b -> ME.rel x y -> ME.rel (smul a x) (smul b y)
  one_smul : ∀ x : MCarrier, ME.rel (smul R.one x) x
  mul_smul :
    ∀ (a b : RCarrier) (x : MCarrier),
      ME.rel (smul (R.mul.op a b) x) (smul a (smul b x))
  smul_add :
    ∀ (a : RCarrier) (x y : MCarrier),
      ME.rel (smul a (M.op x y)) (M.op (smul a x) (smul a y))
  add_smul :
    ∀ (a b : RCarrier) (x : MCarrier),
      ME.rel (smul (R.add.op a b) x) (M.op (smul a x) (smul b x))

namespace RelRing

variable {A : Type u} {r : A -> A -> Prop}

def toRelEquiv (R : RelRing A r) : RelEquiv A where
  rel := r
  refl := R.refl
  symm := R.symm
  trans := R.trans

def toRingUpWith (E : RelEquiv A) (R : RelRing A E.rel) :
    RingUp A E where
  add := {
    op := R.add
    op_congr := R.add_congr
    assoc := R.add_assoc
    one := R.zero
    one_mul := R.zero_add
    mul_one := R.add_zero
    inv := R.neg
    inv_congr := R.neg_congr
    mul_left_inv := R.neg_add
    comm := R.add_comm
  }
  mul := {
    op := R.mul
    op_congr := R.mul_congr
    assoc := R.mul_assoc
    one := R.one
    one_mul := R.one_mul
    mul_one := R.mul_one
  }
  left_distrib := R.left_distrib
  right_distrib := R.right_distrib

def toRingUp (R : RelRing A r) : RingUp A R.toRelEquiv :=
  toRingUpWith R.toRelEquiv R

end RelRing

namespace RelCommRing

variable {A : Type u} {r : A -> A -> Prop}

def toCommRingUpWith (E : RelEquiv A) (R : RelCommRing A E.rel) :
    CommRingUp A E :=
  CommRingUp.mk (toRingUp := RelRing.toRingUpWith E R.toRelRing) R.mul_comm

def toCommRingUp (R : RelCommRing A r) : CommRingUp A R.toRelRing.toRelEquiv :=
  CommRingUp.mk (toRingUp := RelRing.toRingUp R.toRelRing) R.mul_comm

end RelCommRing

instance relRingInstRingUp
    {A : Type u} {E : RelEquiv A} [R : RelRing A E.rel] :
    RingUp A E :=
  RelRing.toRingUpWith E R

instance relCommRingInstCommRingUp
    {A : Type u} {E : RelEquiv A} [R : RelCommRing A E.rel] :
    CommRingUp A E :=
  RelCommRing.toCommRingUpWith E R

end BEDC.Algebra.Rel
