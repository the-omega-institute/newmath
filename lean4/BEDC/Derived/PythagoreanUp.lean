import BEDC.Derived.GaussianUp
import BEDC.Derived.GcdUp

namespace BEDC.Derived.PythagoreanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.GcdUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zsq (x : Z) : Z :=
  Zmul x x

def zsub (x y : Z) : Z :=
  Zadd x (Zneg y)

def zdouble (x : Z) : Z :=
  Zadd x x

def IsPythagorean (a b c : Z) : Prop :=
  Zeq (Zadd (zsq a) (zsq b)) (zsq c)

def euclidA (m n : Z) : Z :=
  zsub (zsq m) (zsq n)

def euclidB (m n : Z) : Z :=
  zdouble (Zmul m n)

def euclidC (m n : Z) : Z :=
  Zadd (zsq m) (zsq n)

structure EuclidTriple where
  a : Z
  b : Z
  c : Z

def euclidTriple (m n : Z) : EuclidTriple :=
  { a := euclidA m n,
    b := euclidB m n,
    c := euclidC m n }

/- 对应 mathlib 的 `PythagoreanTriple` 方程面；证明经由已有 Gaussian norm 乘法导出。 -/
theorem euclidTriple_isPythagorean (m n : Z) :
    IsPythagorean (euclidA m n) (euclidB m n) (euclidC m n) := by
  let z : BEDC.Derived.GaussianUp.GaussInt := { re := m, im := n }
  have normProduct :
      Zeq (BEDC.Derived.GaussianUp.gaussNorm (BEDC.Derived.GaussianUp.gaussMul z z))
        (Zmul (BEDC.Derived.GaussianUp.gaussNorm z)
          (BEDC.Derived.GaussianUp.gaussNorm z)) :=
    BEDC.Derived.GaussianUp.gaussNorm_mul z z
  have reEq :
      Zeq (BEDC.Derived.GaussianUp.gaussMul z z).re (euclidA m n) := by
    exact R.refl (euclidA m n)
  have imEq :
      Zeq (BEDC.Derived.GaussianUp.gaussMul z z).im (euclidB m n) := by
    exact R.add_congr (R.refl (Zmul m n)) (R.mul_comm n m)
  have cEq :
      Zeq (BEDC.Derived.GaussianUp.gaussNorm z) (euclidC m n) := by
    exact R.refl (euclidC m n)
  have leftNorm :
      Zeq (BEDC.Derived.GaussianUp.gaussNorm (BEDC.Derived.GaussianUp.gaussMul z z))
        (Zadd (zsq (euclidA m n)) (zsq (euclidB m n))) := by
    exact R.add_congr (R.mul_congr reEq reEq) (R.mul_congr imEq imEq)
  have rightNorm :
      Zeq (Zmul (BEDC.Derived.GaussianUp.gaussNorm z)
          (BEDC.Derived.GaussianUp.gaussNorm z))
        (zsq (euclidC m n)) := by
    exact R.mul_congr cEq cEq
  exact R.trans (R.symm leftNorm) (R.trans normProduct rightNorm)

theorem euclidTriple_record_isPythagorean (m n : Z) :
    IsPythagorean (euclidTriple m n).a (euclidTriple m n).b
      (euclidTriple m n).c :=
  euclidTriple_isPythagorean m n

abbrev NatOne : BHist :=
  BHist.e1 BHist.Empty

def NatPositive (n : BHist) : Prop :=
  UnaryHistory n ∧ (hsame n BHist.Empty -> False)

def EuclidNatParameters (m n : BHist) : Prop :=
  UnaryHistory m ∧ NatPositive n ∧ NatUnaryStrictPrefix n m

def NatSquare (x xx : BHist) : Prop :=
  BEDC.Derived.PrimeUp.NatMul x x xx

def IsPythagoreanNat (a b c : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧
    ∃ aa : BHist, ∃ bb : BHist, ∃ cc : BHist, ∃ lhs : BHist,
      NatSquare a aa ∧ NatSquare b bb ∧ NatSquare c cc ∧
        BEDC.Derived.NatUp.NatAdd aa bb lhs ∧ hsame lhs cc

def NatCoprime (a b : BHist) : Prop :=
  NatGcd a b NatOne

def IsPrimitivePythagoreanNat (a b c : BHist) : Prop :=
  IsPythagoreanNat a b c ∧ NatCoprime a b ∧ NatCoprime a c ∧ NatCoprime b c

theorem EuclidNatParameters_left_unary {m n : BHist} :
    EuclidNatParameters m n -> UnaryHistory m := by
  intro params
  exact params.left

theorem EuclidNatParameters_right_positive {m n : BHist} :
    EuclidNatParameters m n -> NatPositive n := by
  intro params
  exact params.right.left

theorem IsPrimitivePythagoreanNat_equation {a b c : BHist} :
    IsPrimitivePythagoreanNat a b c -> IsPythagoreanNat a b c := by
  intro primitive
  exact primitive.left

theorem IsPrimitivePythagoreanNat_gcd_ab {a b c : BHist} :
    IsPrimitivePythagoreanNat a b c -> NatCoprime a b := by
  intro primitive
  exact primitive.right.left

theorem IsPrimitivePythagoreanNat_gcd_ac {a b c : BHist} :
    IsPrimitivePythagoreanNat a b c -> NatCoprime a c := by
  intro primitive
  exact primitive.right.right.left

theorem IsPrimitivePythagoreanNat_gcd_bc {a b c : BHist} :
    IsPrimitivePythagoreanNat a b c -> NatCoprime b c := by
  intro primitive
  exact primitive.right.right.right

end BEDC.Derived.PythagoreanUp
