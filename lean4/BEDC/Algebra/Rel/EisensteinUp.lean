import BEDC.Algebra.Rel.Basic
import BEDC.Derived.EisensteinUp

namespace BEDC.Algebra.Rel

abbrev EisInt := BEDC.Derived.EisensteinUp.EisInt
abbrev EisEq := BEDC.Derived.EisensteinUp.EisEq
abbrev eisZero := BEDC.Derived.EisensteinUp.eisZero
abbrev eisOne := BEDC.Derived.EisensteinUp.eisOne
abbrev eisAdd := BEDC.Derived.EisensteinUp.eisAdd
abbrev eisMul := BEDC.Derived.EisensteinUp.eisMul
abbrev eisNeg := BEDC.Derived.EisensteinUp.eisNeg

instance EisensteinUp_RelEquiv : RelEquiv EisInt where
  rel := EisEq
  refl := BEDC.Derived.EisensteinUp.EisEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.EisensteinUp.EisEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.EisensteinUp.EisEq_trans

instance EisensteinUp_RelCommRing : RelCommRing EisInt EisEq where
  zero := eisZero
  one := eisOne
  add := eisAdd
  mul := eisMul
  neg := eisNeg
  refl := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.eq_refl
  symm := by
    intro x y
    exact BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.eq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.mul_respects
  neg_congr := by
    intro x y
    exact BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.neg_respects
  add_assoc := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.add_assoc
  add_comm := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.add_comm
  add_zero := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.add_zero
  zero_add := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.zero_add
  add_neg := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.add_neg
  neg_add := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.neg_add
  mul_assoc := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.mul_assoc
  mul_comm := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.mul_comm
  mul_one := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.mul_one
  one_mul := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.one_mul
  mul_zero := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.mul_zero
  zero_mul := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.zero_mul
  left_distrib := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.left_distrib
  right_distrib := BEDC.Derived.EisensteinUp.EisInt_comm_ring_laws.right_distrib

theorem EisensteinUp_neg_mul (x y : EisInt) :
    EisEq (eisMul (eisNeg x) y) (eisNeg (eisMul x y)) :=
  EisensteinUp_RelCommRing.neg_mul x y

theorem EisensteinUp_neg_neg (x : EisInt) :
    EisEq (eisNeg (eisNeg x)) x :=
  EisensteinUp_RelCommRing.neg_neg x

end BEDC.Algebra.Rel
