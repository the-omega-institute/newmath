import BEDC.Algebra.Rel.Basic
import BEDC.Algebra.Rel.InterfaceSpine
import BEDC.Derived.SplitComplexUp

namespace BEDC.Algebra.Rel

abbrev SplitComplex := BEDC.Derived.SplitComplexUp.SplitComplex
abbrev SplitEq := BEDC.Derived.SplitComplexUp.SplitEq
abbrev splitZero := BEDC.Derived.SplitComplexUp.splitZero
abbrev splitOne := BEDC.Derived.SplitComplexUp.splitOne
abbrev splitJ := BEDC.Derived.SplitComplexUp.splitJ
abbrev splitAdd := BEDC.Derived.SplitComplexUp.splitAdd
abbrev splitMul := BEDC.Derived.SplitComplexUp.splitMul
abbrev splitNeg := BEDC.Derived.SplitComplexUp.splitNeg
abbrev splitConj := BEDC.Derived.SplitComplexUp.splitConj
abbrev splitNorm := BEDC.Derived.SplitComplexUp.splitNorm

instance SplitComplexUp_RelEquiv : RelEquiv SplitComplex where
  rel := SplitEq
  refl := BEDC.Derived.SplitComplexUp.SplitEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.SplitComplexUp.SplitEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.SplitComplexUp.SplitEq_trans

instance SplitComplexUp_RelCommRing : RelCommRing SplitComplex SplitEq where
  zero := splitZero
  one := splitOne
  add := splitAdd
  mul := splitMul
  neg := splitNeg
  refl := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.eq_refl
  symm := by
    intro x y
    exact BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.eq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.mul_respects
  neg_congr := by
    intro x y
    exact BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.neg_respects
  add_assoc := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.add_assoc
  add_comm := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.add_comm
  add_zero := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.add_zero
  zero_add := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.zero_add
  add_neg := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.add_neg
  neg_add := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.neg_add
  mul_assoc := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.mul_assoc
  mul_comm := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.mul_comm
  mul_one := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.mul_one
  one_mul := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.one_mul
  mul_zero := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.mul_zero
  zero_mul := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.zero_mul
  left_distrib := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.left_distrib
  right_distrib := BEDC.Derived.SplitComplexUp.SplitComplex_comm_ring_laws.right_distrib

instance SplitComplexUp_CommRingUp : CommRingUp SplitComplex SplitComplexUp_RelEquiv :=
  RelCommRing.toCommRingUpWith SplitComplexUp_RelEquiv SplitComplexUp_RelCommRing

theorem SplitComplexUp_neg_mul (x y : SplitComplex) :
    SplitEq (splitMul (splitNeg x) y) (splitNeg (splitMul x y)) :=
  SplitComplexUp_RelCommRing.neg_mul x y

theorem SplitComplexUp_mul_neg (x y : SplitComplex) :
    SplitEq (splitMul x (splitNeg y)) (splitNeg (splitMul x y)) :=
  SplitComplexUp_RelCommRing.mul_neg x y

theorem SplitComplexUp_neg_neg (x : SplitComplex) :
    SplitEq (splitNeg (splitNeg x)) x :=
  SplitComplexUp_RelCommRing.neg_neg x

end BEDC.Algebra.Rel
