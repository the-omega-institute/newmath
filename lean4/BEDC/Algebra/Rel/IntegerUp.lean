import BEDC.Algebra.Rel.RingEquiv
import BEDC.Algebra.Rel.InterfaceSpine
import BEDC.Derived.IntUp.CommRingCore

namespace BEDC.Algebra.Rel

abbrev IntegerUp := BEDC.Derived.PrimeUp.IntegerUp
abbrev IntEq := BEDC.Derived.RationalUp.IntEq
abbrev intZero := BEDC.Derived.RationalUp.intZero
abbrev intOne := BEDC.Derived.RationalUp.intOne
abbrev IntAdd := BEDC.Derived.RationalUp.IntAdd
abbrev IntMul := BEDC.Derived.RationalUp.IntMul
abbrev IntNeg := BEDC.Derived.RationalUp.IntNeg

instance IntegerUp_RelEquiv : RelEquiv IntegerUp where
  rel := IntEq
  refl := BEDC.Derived.RationalUp.IntEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.RationalUp.IntEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.RationalUp.IntEq_trans

instance IntegerUp_RelCommRing : RelCommRing IntegerUp IntEq where
  zero := intZero
  one := intOne
  add := IntAdd
  mul := IntMul
  neg := IntNeg
  refl := BEDC.Derived.RationalUp.IntEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.RationalUp.IntEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.RationalUp.IntEq_trans
  add_congr := by
    intro x x' y y'
    exact BEDC.Derived.RationalUp.IntAdd_respects
  mul_congr := by
    intro x x' y y'
    exact BEDC.Derived.RationalUp.IntMul_respects
  neg_congr := by
    intro x y
    exact BEDC.Derived.RationalUp.IntNeg_respects
  add_assoc := BEDC.Derived.RationalUp.IntAdd_assoc
  add_comm := BEDC.Derived.RationalUp.IntAdd_comm
  add_zero := BEDC.Derived.RationalUp.IntAdd_zero
  zero_add := BEDC.Derived.RationalUp.IntAdd_zero_left
  add_neg := BEDC.Derived.RationalUp.IntAdd_neg
  neg_add := BEDC.Derived.RationalUp.IntAdd_neg_left
  mul_assoc := BEDC.Derived.RationalUp.IntMul_assoc
  mul_comm := BEDC.Derived.RationalUp.IntMul_comm
  mul_one := BEDC.Derived.RationalUp.IntMul_one
  one_mul := BEDC.Derived.RationalUp.IntMul_one_left
  mul_zero := BEDC.Derived.RationalUp.IntMul_zero
  zero_mul := BEDC.Derived.RationalUp.IntMul_zero_left
  left_distrib := BEDC.Derived.RationalUp.IntMul_add_distrib
  right_distrib := BEDC.Derived.RationalUp.IntMul_add_distrib_right

instance IntegerUp_CommRingUp : CommRingUp IntegerUp IntegerUp_RelEquiv :=
  RelCommRing.toCommRingUpWith IntegerUp_RelEquiv IntegerUp_RelCommRing

theorem IntegerUp_sub_eq_add_neg (x y : IntegerUp) :
    IntEq (IntegerUp_RelCommRing.sub x y) (IntAdd x (IntNeg y)) :=
  IntegerUp_RelCommRing.sub_eq_add_neg x y

theorem IntegerUp_neg_mul (x y : IntegerUp) :
    IntEq (IntMul (IntNeg x) y) (IntNeg (IntMul x y)) :=
  IntegerUp_RelCommRing.neg_mul x y

theorem IntegerUp_mul_neg (x y : IntegerUp) :
    IntEq (IntMul x (IntNeg y)) (IntNeg (IntMul x y)) :=
  IntegerUp_RelCommRing.mul_neg x y

theorem IntegerUp_neg_neg (x : IntegerUp) :
    IntEq (IntNeg (IntNeg x)) x :=
  IntegerUp_RelCommRing.neg_neg x

end BEDC.Algebra.Rel
