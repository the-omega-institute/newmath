import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.RationalUp

def IntegerUp_comm_ring_laws : IntegerUpCommRingLaws where
  eq_refl := BEDC.Algebra.Rel.IntegerUp_RelCommRing.refl
  eq_symm := BEDC.Algebra.Rel.IntegerUp_RelCommRing.symm
  eq_trans := BEDC.Algebra.Rel.IntegerUp_RelCommRing.trans
  add_respects := BEDC.Algebra.Rel.IntegerUp_RelCommRing.add_congr
  mul_respects := BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_congr
  neg_respects := BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_congr
  add_comm := BEDC.Algebra.Rel.IntegerUp_RelCommRing.add_comm
  add_assoc := BEDC.Algebra.Rel.IntegerUp_RelCommRing.add_assoc
  add_zero := BEDC.Algebra.Rel.IntegerUp_RelCommRing.add_zero
  zero_add := BEDC.Algebra.Rel.IntegerUp_RelCommRing.zero_add
  add_neg := BEDC.Algebra.Rel.IntegerUp_RelCommRing.add_neg
  neg_add := BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_add
  mul_comm := BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_comm
  mul_assoc := BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_assoc
  mul_one := BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_one
  one_mul := BEDC.Algebra.Rel.IntegerUp_RelCommRing.one_mul
  mul_zero := BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_zero
  zero_mul := BEDC.Algebra.Rel.IntegerUp_RelCommRing.zero_mul
  left_distrib := BEDC.Algebra.Rel.IntegerUp_RelCommRing.left_distrib
  right_distrib := BEDC.Algebra.Rel.IntegerUp_RelCommRing.right_distrib

end BEDC.Derived.RationalUp

namespace BEDC.Derived.IntUp

abbrev IntegerUpCommRingLaws :=
  BEDC.Derived.RationalUp.IntegerUpCommRingLaws

theorem IntAdd_respects {a a' b b' : BEDC.Derived.PrimeUp.IntegerUp} :
    BEDC.Derived.RationalUp.IntEq a a' ->
      BEDC.Derived.RationalUp.IntEq b b' ->
        BEDC.Derived.RationalUp.IntEq
          (BEDC.Derived.RationalUp.IntAdd a b)
          (BEDC.Derived.RationalUp.IntAdd a' b') :=
  BEDC.Derived.RationalUp.IntAdd_respects

theorem IntMul_respects {a a' b b' : BEDC.Derived.PrimeUp.IntegerUp} :
    BEDC.Derived.RationalUp.IntEq a a' ->
      BEDC.Derived.RationalUp.IntEq b b' ->
        BEDC.Derived.RationalUp.IntEq
          (BEDC.Derived.RationalUp.IntMul a b)
          (BEDC.Derived.RationalUp.IntMul a' b') :=
  BEDC.Derived.RationalUp.IntMul_respects

theorem IntNeg_respects {a b : BEDC.Derived.PrimeUp.IntegerUp} :
    BEDC.Derived.RationalUp.IntEq a b ->
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntNeg a)
        (BEDC.Derived.RationalUp.IntNeg b) :=
  BEDC.Derived.RationalUp.IntNeg_respects

theorem IntAdd_comm (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd a b)
      (BEDC.Derived.RationalUp.IntAdd b a) :=
  BEDC.Derived.RationalUp.IntAdd_comm a b

theorem IntAdd_assoc (a b c : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd (BEDC.Derived.RationalUp.IntAdd a b) c)
      (BEDC.Derived.RationalUp.IntAdd a (BEDC.Derived.RationalUp.IntAdd b c)) :=
  BEDC.Derived.RationalUp.IntAdd_assoc a b c

theorem IntAdd_zero (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd a BEDC.Derived.RationalUp.intZero) a :=
  BEDC.Derived.RationalUp.IntAdd_zero a

private theorem IntAdd_zero_left (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd BEDC.Derived.RationalUp.intZero a) a :=
  BEDC.Derived.RationalUp.IntAdd_zero_left a

theorem IntAdd_neg (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd a (BEDC.Derived.RationalUp.IntNeg a))
      BEDC.Derived.RationalUp.intZero :=
  BEDC.Derived.RationalUp.IntAdd_neg a

private theorem IntAdd_neg_left (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntAdd (BEDC.Derived.RationalUp.IntNeg a) a)
      BEDC.Derived.RationalUp.intZero :=
  BEDC.Derived.RationalUp.IntAdd_neg_left a

theorem IntMul_comm (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul a b)
      (BEDC.Derived.RationalUp.IntMul b a) :=
  BEDC.Derived.RationalUp.IntMul_comm a b

theorem IntMul_assoc (a b c : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul (BEDC.Derived.RationalUp.IntMul a b) c)
      (BEDC.Derived.RationalUp.IntMul a (BEDC.Derived.RationalUp.IntMul b c)) :=
  BEDC.Derived.RationalUp.IntMul_assoc a b c

theorem IntMul_one (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul a BEDC.Derived.RationalUp.intOne) a :=
  BEDC.Derived.RationalUp.IntMul_one a

private theorem IntMul_one_left (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intOne a) a :=
  BEDC.Derived.RationalUp.IntMul_one_left a

theorem IntMul_zero (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul a BEDC.Derived.RationalUp.intZero)
      BEDC.Derived.RationalUp.intZero :=
  BEDC.Derived.RationalUp.IntMul_zero a

private theorem IntMul_zero_left (a : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero a)
      BEDC.Derived.RationalUp.intZero :=
  BEDC.Derived.RationalUp.IntMul_zero_left a

theorem IntMul_add_distrib (a b c : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul a (BEDC.Derived.RationalUp.IntAdd b c))
      (BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul a b)
        (BEDC.Derived.RationalUp.IntMul a c)) :=
  BEDC.Derived.RationalUp.IntMul_add_distrib a b c

theorem IntMul_add_distrib_right (a b c : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul (BEDC.Derived.RationalUp.IntAdd a b) c)
      (BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul a c)
        (BEDC.Derived.RationalUp.IntMul b c)) :=
  BEDC.Derived.RationalUp.IntMul_add_distrib_right a b c

def IntegerUp_comm_ring_laws : IntegerUpCommRingLaws :=
  BEDC.Derived.RationalUp.IntegerUp_comm_ring_laws

end BEDC.Derived.IntUp
