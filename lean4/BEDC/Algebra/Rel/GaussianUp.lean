import BEDC.Algebra.Rel.Basic
import BEDC.Derived.GaussianUp

namespace BEDC.Algebra.Rel

abbrev GaussInt := BEDC.Derived.GaussianUp.GaussInt
abbrev GaussEq := BEDC.Derived.GaussianUp.GaussEq
abbrev gaussZero := BEDC.Derived.GaussianUp.gaussZero
abbrev gaussOne := BEDC.Derived.GaussianUp.gaussOne
abbrev gaussAdd := BEDC.Derived.GaussianUp.gaussAdd
abbrev gaussMul := BEDC.Derived.GaussianUp.gaussMul
abbrev gaussNeg := BEDC.Derived.GaussianUp.gaussNeg

instance GaussianUp_RelEquiv : RelEquiv GaussInt where
  rel := GaussEq
  refl := BEDC.Derived.GaussianUp.GaussEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.GaussianUp.GaussEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.GaussianUp.GaussEq_trans

instance GaussianUp_RelCommRing : RelCommRing GaussInt GaussEq where
  zero := gaussZero
  one := gaussOne
  add := gaussAdd
  mul := gaussMul
  neg := gaussNeg
  refl := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.eq_refl
  symm := by
    intro x y
    exact BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.eq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.mul_respects
  neg_congr := by
    intro x y
    exact BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.neg_respects
  add_assoc := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.add_assoc
  add_comm := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.add_comm
  add_zero := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.add_zero
  zero_add := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.zero_add
  add_neg := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.add_neg
  neg_add := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.neg_add
  mul_assoc := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.mul_assoc
  mul_comm := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.mul_comm
  mul_one := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.mul_one
  one_mul := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.one_mul
  mul_zero := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.mul_zero
  zero_mul := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.zero_mul
  left_distrib := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.left_distrib
  right_distrib := BEDC.Derived.GaussianUp.GaussInt_comm_ring_laws.right_distrib

theorem GaussianUp_neg_mul (x y : GaussInt) :
    GaussEq (gaussMul (gaussNeg x) y) (gaussNeg (gaussMul x y)) :=
  GaussianUp_RelCommRing.neg_mul x y

theorem GaussianUp_neg_neg (x : GaussInt) :
    GaussEq (gaussNeg (gaussNeg x)) x :=
  GaussianUp_RelCommRing.neg_neg x

end BEDC.Algebra.Rel
