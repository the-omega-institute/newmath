import BEDC.Algebra.Rel.InterfaceSpine

namespace BEDC.Derived.BooleanRingUp

open BEDC.Algebra.Rel

universe u

def RingIdempotent {A : Type u} {r : A -> A -> Prop}
    (R : RelRing A r) (x : A) : Prop :=
  r (R.mul x x) x

structure BooleanRelRing (A : Type u) (r : A -> A -> Prop) where
  ring : RelRing A r
  idempotent : forall x : A, RingIdempotent ring x

namespace BooleanRelRing

variable {A : Type u} {r : A -> A -> Prop}

theorem one_add_one_eq_zero (B : BooleanRelRing A r) :
    r (B.ring.add B.ring.one B.ring.one) B.ring.zero := by
  let R := B.ring
  let two := R.add R.one R.one
  have hDistrib :
      r (R.mul two two)
        (R.add (R.mul R.one two) (R.mul R.one two)) :=
    R.right_distrib R.one R.one two
  have hUnits :
      r (R.add (R.mul R.one two) (R.mul R.one two)) (R.add two two) :=
    R.add_congr (R.one_mul two) (R.one_mul two)
  have hSquareToDouble : r (R.mul two two) (R.add two two) :=
    R.trans hDistrib hUnits
  have hDoubleToTwo : r (R.add two two) two :=
    R.trans (R.symm hSquareToDouble) (B.idempotent two)
  exact GroupUp.mul_right_cancel (RelRing.toRingUp R).add.toGroupUp
    (R.trans hDoubleToTwo (R.symm (R.zero_add two)))

theorem add_self_zero (B : BooleanRelRing A r) (x : A) :
    r (B.ring.add x x) B.ring.zero := by
  let R := B.ring
  let two := R.add R.one R.one
  have hUnits :
      r (R.add x x) (R.add (R.mul x R.one) (R.mul x R.one)) :=
    R.add_congr (R.symm (R.mul_one x)) (R.symm (R.mul_one x))
  have hDistrib :
      r (R.add (R.mul x R.one) (R.mul x R.one)) (R.mul x two) :=
    R.symm (R.left_distrib x R.one R.one)
  have hTwo :
      r (R.mul x two) (R.mul x R.zero) :=
    R.mul_congr (R.refl x) (B.one_add_one_eq_zero)
  exact R.trans hUnits (R.trans hDistrib (R.trans hTwo (R.mul_zero x)))

theorem square_add_expand (B : BooleanRelRing A r) (x y : A) :
    r (B.ring.mul (B.ring.add x y) (B.ring.add x y))
      (B.ring.add (B.ring.add (B.ring.mul x x) (B.ring.mul x y))
        (B.ring.add (B.ring.mul y x) (B.ring.mul y y))) := by
  let R := B.ring
  have hOuter :
      r (R.mul (R.add x y) (R.add x y))
        (R.add (R.mul x (R.add x y)) (R.mul y (R.add x y))) :=
    R.right_distrib x y (R.add x y)
  have hInner :
      r (R.add (R.mul x (R.add x y)) (R.mul y (R.add x y)))
        (R.add (R.add (R.mul x x) (R.mul x y))
          (R.add (R.mul y x) (R.mul y y))) :=
    R.add_congr (R.left_distrib x x y) (R.left_distrib y x y)
  exact R.trans hOuter hInner

theorem cross_terms_sum_zero (B : BooleanRelRing A r) (x y : A) :
    r (B.ring.add (B.ring.mul x y) (B.ring.mul y x)) B.ring.zero := by
  let R := B.ring
  let xy := R.mul x y
  let yx := R.mul y x
  have hExpand :
      r (R.mul (R.add x y) (R.add x y))
        (R.add (R.add (R.mul x x) xy) (R.add yx (R.mul y y))) :=
    B.square_add_expand x y
  have hNormalize :
      r (R.add (R.add (R.mul x x) xy) (R.add yx (R.mul y y)))
        (R.add (R.add x xy) (R.add yx y)) :=
    R.add_congr
      (R.add_congr (B.idempotent x) (R.refl xy))
      (R.add_congr (R.refl yx) (B.idempotent y))
  have hNormalizedToSum :
      r (R.add (R.add x xy) (R.add yx y)) (R.add x y) :=
    R.trans (R.symm hNormalize)
      (R.trans (R.symm hExpand) (B.idempotent (R.add x y)))
  have hRebracket :
      r (R.add (R.add x xy) (R.add yx y))
        (R.add x (R.add (R.add xy yx) y)) := by
    have hFirst :
        r (R.add (R.add x xy) (R.add yx y))
          (R.add x (R.add xy (R.add yx y))) :=
      R.add_assoc x xy (R.add yx y)
    have hSecond :
        r (R.add x (R.add xy (R.add yx y)))
          (R.add x (R.add (R.add xy yx) y)) :=
      R.add_congr (R.refl x) (R.symm (R.add_assoc xy yx y))
    exact R.trans hFirst hSecond
  have hCancelLeftInput :
      r (R.add x (R.add (R.add xy yx) y)) (R.add x y) :=
    R.trans (R.symm hRebracket) hNormalizedToSum
  have hCancelLeft :
      r (R.add (R.add xy yx) y) y :=
    GroupUp.mul_left_cancel (RelRing.toRingUp R).add.toGroupUp hCancelLeftInput
  exact GroupUp.mul_right_cancel (RelRing.toRingUp R).add.toGroupUp
    (R.trans hCancelLeft (R.symm (R.zero_add y)))

theorem mul_comm (B : BooleanRelRing A r) (x y : A) :
    r (B.ring.mul x y) (B.ring.mul y x) := by
  let R := B.ring
  let xy := R.mul x y
  let yx := R.mul y x
  have hSumZero : r (R.add xy yx) R.zero :=
    B.cross_terms_sum_zero x y
  have hyxToNegXy : r yx (R.neg xy) :=
    R.eq_neg_of_add_eq_zero hSumZero
  have hNegXyToXy : r (R.neg xy) xy :=
    R.neg_eq_of_add_eq_zero (B.add_self_zero xy)
  exact R.symm (R.trans hyxToNegXy hNegXyToXy)

def toRelCommRing (B : BooleanRelRing A r) : RelCommRing A r where
  toRelRing := B.ring
  mul_comm := B.mul_comm

theorem every_element_idempotent (B : BooleanRelRing A r) (x : A) :
    RingIdempotent B.ring x :=
  B.idempotent x

end BooleanRelRing

structure BooleanRingUp (A : Type u) (E : RelEquiv A) where
  ring : RingUp A E
  idempotent : forall x : A, E.rel (ring.mul.op x x) x

namespace BooleanRingUp

variable {A : Type u} {E : RelEquiv A}

def toBooleanRelRing (B : BooleanRingUp A E) : BooleanRelRing A E.rel where
  ring := RingUp.toRelRing B.ring
  idempotent := B.idempotent

theorem add_self_zero (B : BooleanRingUp A E) (x : A) :
    E.rel (B.ring.add.op x x) B.ring.zero :=
  B.toBooleanRelRing.add_self_zero x

theorem mul_comm (B : BooleanRingUp A E) (x y : A) :
    E.rel (B.ring.mul.op x y) (B.ring.mul.op y x) :=
  B.toBooleanRelRing.mul_comm x y

def toCommRingUp (B : BooleanRingUp A E) : CommRingUp A E where
  toRingUp := B.ring
  mul_comm := B.mul_comm

theorem every_element_idempotent (B : BooleanRingUp A E) (x : A) :
    E.rel (B.ring.mul.op x x) x :=
  B.idempotent x

end BooleanRingUp

structure BooleanAlgebraUp (A : Type u) (E : RelEquiv A) where
  meet : A -> A -> A
  join : A -> A -> A
  compl : A -> A
  xor : A -> A -> A
  bot : A
  top : A
  meet_congr :
    forall {x x' y y' : A}, E.rel x x' -> E.rel y y' ->
      E.rel (meet x y) (meet x' y')
  join_congr :
    forall {x x' y y' : A}, E.rel x x' -> E.rel y y' ->
      E.rel (join x y) (join x' y')
  compl_congr : forall {x y : A}, E.rel x y -> E.rel (compl x) (compl y)
  xor_congr :
    forall {x x' y y' : A}, E.rel x x' -> E.rel y y' ->
      E.rel (xor x y) (xor x' y')
  xor_assoc : forall x y z : A, E.rel (xor (xor x y) z) (xor x (xor y z))
  xor_comm : forall x y : A, E.rel (xor x y) (xor y x)
  xor_bot : forall x : A, E.rel (xor x bot) x
  bot_xor : forall x : A, E.rel (xor bot x) x
  xor_self : forall x : A, E.rel (xor x x) bot
  meet_assoc : forall x y z : A, E.rel (meet (meet x y) z) (meet x (meet y z))
  meet_top : forall x : A, E.rel (meet x top) x
  top_meet : forall x : A, E.rel (meet top x) x
  meet_bot : forall x : A, E.rel (meet x bot) bot
  bot_meet : forall x : A, E.rel (meet bot x) bot
  meet_self : forall x : A, E.rel (meet x x) x
  meet_comm : forall x y : A, E.rel (meet x y) (meet y x)
  meet_left_distrib_xor :
    forall x y z : A, E.rel (meet x (xor y z)) (xor (meet x y) (meet x z))
  meet_right_distrib_xor :
    forall x y z : A, E.rel (meet (xor x y) z) (xor (meet x z) (meet y z))
  xor_is_symmetric_difference :
    forall x y : A,
      E.rel (xor x y) (join (meet x (compl y)) (meet (compl x) y))
  meet_compl : forall x : A, E.rel (meet x (compl x)) bot
  join_compl : forall x : A, E.rel (join x (compl x)) top

namespace BooleanAlgebraUp

variable {A : Type u} {E : RelEquiv A}

def symmetricDifference (B : BooleanAlgebraUp A E) (x y : A) : A :=
  B.join (B.meet x (B.compl y)) (B.meet (B.compl x) y)

theorem xor_eq_symmetricDifference (B : BooleanAlgebraUp A E) (x y : A) :
    E.rel (B.xor x y) (B.symmetricDifference x y) :=
  B.xor_is_symmetric_difference x y

def toBooleanRing (B : BooleanAlgebraUp A E) : BooleanRingUp A E where
  ring := {
    add := {
      op := B.xor
      op_congr := B.xor_congr
      assoc := B.xor_assoc
      one := B.bot
      one_mul := B.bot_xor
      mul_one := B.xor_bot
      inv := fun x => x
      inv_congr := by
        intro x y sameXY
        exact sameXY
      mul_left_inv := B.xor_self
      comm := B.xor_comm
    }
    mul := {
      op := B.meet
      op_congr := B.meet_congr
      assoc := B.meet_assoc
      one := B.top
      one_mul := B.top_meet
      mul_one := B.meet_top
    }
    left_distrib := B.meet_left_distrib_xor
    right_distrib := B.meet_right_distrib_xor
  }
  idempotent := B.meet_self

theorem toBooleanRing_add_is_symmetric_difference
    (B : BooleanAlgebraUp A E) (x y : A) :
    E.rel (B.toBooleanRing.ring.add.op x y) (B.symmetricDifference x y) :=
  B.xor_eq_symmetricDifference x y

theorem toBooleanRing_mul_is_meet (B : BooleanAlgebraUp A E) (x y : A) :
    E.rel (B.toBooleanRing.ring.mul.op x y) (B.meet x y) :=
  E.refl (B.meet x y)

theorem toBooleanRing_char_two (B : BooleanAlgebraUp A E) (x : A) :
    E.rel (B.toBooleanRing.ring.add.op x x) B.toBooleanRing.ring.zero :=
  B.toBooleanRing.add_self_zero x

theorem toBooleanRing_mul_comm (B : BooleanAlgebraUp A E) (x y : A) :
    E.rel (B.toBooleanRing.ring.mul.op x y) (B.toBooleanRing.ring.mul.op y x) :=
  B.toBooleanRing.mul_comm x y

end BooleanAlgebraUp

structure BooleanAlgebraOps (A : Type u) (E : RelEquiv A) where
  meet : A -> A -> A
  join : A -> A -> A
  compl : A -> A
  symmetricDifference : A -> A -> A
  bot : A
  top : A

namespace BooleanAlgebraOps

variable {A : Type u} {E : RelEquiv A}

def fromBooleanRing (B : BooleanRingUp A E) : BooleanAlgebraOps A E where
  meet := B.ring.mul.op
  join := fun x y => B.ring.add.op (B.ring.add.op x y) (B.ring.mul.op x y)
  compl := fun x => B.ring.add.op B.ring.one x
  symmetricDifference := B.ring.add.op
  bot := B.ring.zero
  top := B.ring.one

theorem fromBooleanRing_meet_is_mul (B : BooleanRingUp A E) (x y : A) :
    E.rel ((fromBooleanRing B).meet x y) (B.ring.mul.op x y) :=
  E.refl (B.ring.mul.op x y)

theorem fromBooleanRing_symmetricDifference_is_add
    (B : BooleanRingUp A E) (x y : A) :
    E.rel ((fromBooleanRing B).symmetricDifference x y) (B.ring.add.op x y) :=
  E.refl (B.ring.add.op x y)

theorem fromBooleanRing_compl_is_one_add (B : BooleanRingUp A E) (x : A) :
    E.rel ((fromBooleanRing B).compl x) (B.ring.add.op B.ring.one x) :=
  E.refl (B.ring.add.op B.ring.one x)

theorem fromBooleanRing_join_is_add_add_mul (B : BooleanRingUp A E) (x y : A) :
    E.rel ((fromBooleanRing B).join x y)
      (B.ring.add.op (B.ring.add.op x y) (B.ring.mul.op x y)) :=
  E.refl (B.ring.add.op (B.ring.add.op x y) (B.ring.mul.op x y))

end BooleanAlgebraOps

theorem boolean_relring_add_self_zero {A : Type u} {r : A -> A -> Prop}
    (B : BooleanRelRing A r) (x : A) :
    r (B.ring.add x x) B.ring.zero :=
  B.add_self_zero x

theorem boolean_relring_mul_comm {A : Type u} {r : A -> A -> Prop}
    (B : BooleanRelRing A r) (x y : A) :
    r (B.ring.mul x y) (B.ring.mul y x) :=
  B.mul_comm x y

theorem boolean_ring_add_self_zero {A : Type u} {E : RelEquiv A}
    (B : BooleanRingUp A E) (x : A) :
    E.rel (B.ring.add.op x x) B.ring.zero :=
  B.add_self_zero x

theorem boolean_ring_mul_comm {A : Type u} {E : RelEquiv A}
    (B : BooleanRingUp A E) (x y : A) :
    E.rel (B.ring.mul.op x y) (B.ring.mul.op y x) :=
  B.mul_comm x y

end BEDC.Derived.BooleanRingUp
