import BEDC.Algebra.Rel.Basic
import BEDC.Algebra.Rel.InterfaceSpine
import BEDC.Derived.QuadIntUp

namespace BEDC.Algebra.Rel

abbrev QuadInt := BEDC.Derived.QuadIntUp.QuadInt
abbrev QuadEq {d : IntegerUp} := BEDC.Derived.QuadIntUp.QuadEq (d := d)
abbrev quadZero {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadZero (d := d)
abbrev quadOne {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadOne (d := d)
abbrev quadSqrt {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadSqrt (d := d)
abbrev quadAdd {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadAdd (d := d)
abbrev quadMul {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadMul (d := d)
abbrev quadNeg {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadNeg (d := d)
abbrev quadConj {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadConj (d := d)
abbrev quadNorm {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadNorm (d := d)
abbrev quadOfInt {d : IntegerUp} := BEDC.Derived.QuadIntUp.quadOfInt (d := d)
abbrev GaussianQuadInt := BEDC.Derived.QuadIntUp.GaussianQuadInt
abbrev gaussianQuadParameter := BEDC.Derived.QuadIntUp.gaussianQuadParameter

abbrev QuadIntUp_RelCommRing (d : IntegerUp) :
    RelCommRing (QuadInt d) (QuadEq (d := d)) :=
  BEDC.Derived.QuadIntUp.QuadInt_RelCommRing d

abbrev QuadIntUp_RelEquiv (d : IntegerUp) :
    RelEquiv (QuadInt d) :=
  BEDC.Derived.QuadIntUp.QuadInt_RelEquiv d

instance QuadIntUp_CommRingUp (d : IntegerUp) :
    CommRingUp (QuadInt d) (QuadIntUp_RelEquiv d) :=
  RelCommRing.toCommRingUpWith (QuadIntUp_RelEquiv d) (QuadIntUp_RelCommRing d)

theorem QuadIntUp_norm_mul (d : IntegerUp) (x y : QuadInt d) :
    IntEq (quadNorm (quadMul x y)) (IntMul (quadNorm x) (quadNorm y)) :=
  BEDC.Derived.QuadIntUp.quadNorm_mul x y

theorem QuadIntUp_sqrt_mul_self (d : IntegerUp) :
    QuadEq (quadMul (quadSqrt (d := d)) quadSqrt) (quadOfInt d) :=
  BEDC.Derived.QuadIntUp.quadSqrt_mul_self

theorem QuadIntUp_neg_mul (d : IntegerUp) (x y : QuadInt d) :
    QuadEq (quadMul (quadNeg x) y) (quadNeg (quadMul x y)) :=
  (QuadIntUp_RelCommRing d).neg_mul x y

theorem QuadIntUp_mul_neg (d : IntegerUp) (x y : QuadInt d) :
    QuadEq (quadMul x (quadNeg y)) (quadNeg (quadMul x y)) :=
  (QuadIntUp_RelCommRing d).mul_neg x y

theorem QuadIntUp_neg_neg (d : IntegerUp) (x : QuadInt d) :
    QuadEq (quadNeg (quadNeg x)) x :=
  (QuadIntUp_RelCommRing d).neg_neg x

end BEDC.Algebra.Rel
