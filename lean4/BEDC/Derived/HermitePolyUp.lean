import BEDC.Algebra.FiniteFold
import BEDC.Derived.PolynomialUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.BesselNumberUp

namespace BEDC.Derived.HermitePolyUp

abbrev IntegerUp := BEDC.Derived.PolynomialUp.IntegerUp
abbrev Poly := BEDC.Derived.PolynomialUp.Poly

abbrev zZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

abbrev zOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

abbrev zNeg : IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntNeg

abbrev zNat (n : Nat) : IntegerUp :=
  BEDC.Derived.PolynomialUp.coeffOfNat n

abbrev polyAdd : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyAdd

abbrev polyMul : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyMul

abbrev polyNeg : Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyNeg

abbrev polyScale : IntegerUp -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyScale

def hermiteX : Poly :=
  [zZero, zOne]

-- 概率论规范的 Hermite 族: `He 0 = 1`, `He 1 = x`,
-- `He (n + 2) = x * He (n + 1) - (n + 1) * He n`.
def hermiteRecurrencePoly : Nat -> Poly
  | 0 => [zOne]
  | Nat.succ 0 => hermiteX
  | Nat.succ (Nat.succ n) =>
      polyAdd
        (polyMul hermiteX (hermiteRecurrencePoly (Nat.succ n)))
        (polyNeg (polyScale (zNat (Nat.succ n)) (hermiteRecurrencePoly n)))

def hermiteSignedNat : Nat -> Nat -> IntegerUp
  | 0, n => zNat n
  | Nat.succ k, n => zNeg (hermiteSignedNat k n)

def hermiteUnsignedCoefficient (n k : Nat) : Nat :=
  BEDC.Derived.BesselNumberUp.besselNumber n k

def hermiteSignedCoefficient (n k : Nat) : IntegerUp :=
  hermiteSignedNat k (hermiteUnsignedCoefficient n k)

def hermiteFactorialRatioMagnitude (n k : Nat) : Nat :=
  BEDC.Derived.BesselNumberUp.besselClosedFormula n k

def hermiteFactorialRatioCoefficient (n k : Nat) : IntegerUp :=
  hermiteSignedNat k (hermiteFactorialRatioMagnitude n k)

def zeroCoefficients : Nat -> Poly
  | 0 => []
  | Nat.succ n => zZero :: zeroCoefficients n

def hermiteMonomial (degree : Nat) (coefficient : IntegerUp) : Poly :=
  zeroCoefficients degree ++ [coefficient]

def hermiteExplicitTerm (n k : Nat) : Poly :=
  hermiteMonomial (n - (k + k)) (hermiteFactorialRatioCoefficient n k)

def hermiteExplicitPrefix (n : Nat) : Nat -> Poly
  | 0 => hermiteExplicitTerm n 0
  | Nat.succ k =>
      polyAdd (hermiteExplicitPrefix n k)
        (hermiteExplicitTerm n (Nat.succ k))

def hermiteExplicitSparsePoly (n : Nat) : Poly :=
  hermiteExplicitPrefix n n

def hermiteCoefficientSearch (n degree : Nat) : Nat -> Nat -> IntegerUp
  | 0, k =>
      if degree + (k + k) = n then hermiteFactorialRatioCoefficient n k else zZero
  | Nat.succ fuel, k =>
      if degree + (k + k) = n then hermiteFactorialRatioCoefficient n k
      else hermiteCoefficientSearch n degree fuel (Nat.succ k)

def hermiteCanonicalCoefficient (n degree : Nat) : IntegerUp :=
  hermiteCoefficientSearch n degree n 0

def hermiteCanonicalPrefix (n : Nat) : Nat -> Poly
  | 0 => [hermiteCanonicalCoefficient n 0]
  | Nat.succ degree =>
      hermiteCanonicalPrefix n degree ++
        [hermiteCanonicalCoefficient n (Nat.succ degree)]

def hermiteExplicitPoly (n : Nat) : Poly :=
  hermiteCanonicalPrefix n n

-- 概率论归一化下的形式 Gaussian 矩:
-- `M 0 = 1`, `M 1 = 0`, `M (n + 2) = (n + 1) M n`.
def gaussianMoment : Nat -> Nat
  | 0 => 1
  | Nat.succ 0 => 0
  | Nat.succ (Nat.succ n) => Nat.succ n * gaussianMoment n

def coefficientMomentTerm (degree : Nat) (coefficient : IntegerUp) : IntegerUp :=
  BEDC.Derived.RationalUp.IntMul coefficient (zNat (gaussianMoment degree))

def polynomialGaussianMomentFrom : Nat -> Poly -> IntegerUp
  | _, [] => zZero
  | degree, coefficient :: rest =>
      BEDC.Derived.RationalUp.IntAdd
        (coefficientMomentTerm degree coefficient)
        (polynomialGaussianMomentFrom (Nat.succ degree) rest)

def polynomialGaussianMoment (p : Poly) : IntegerUp :=
  polynomialGaussianMomentFrom 0 p

def hermiteGaussianInner (p q : Poly) : IntegerUp :=
  polynomialGaussianMoment (polyMul p q)

theorem hermiteRecurrencePoly_zero :
    hermiteRecurrencePoly 0 = [zOne] := by
  rfl

theorem hermiteRecurrencePoly_one :
    hermiteRecurrencePoly 1 = hermiteX := by
  rfl

theorem hermiteRecurrencePoly_succ_succ (n : Nat) :
    hermiteRecurrencePoly (Nat.succ (Nat.succ n)) =
      polyAdd
        (polyMul hermiteX (hermiteRecurrencePoly (Nat.succ n)))
        (polyNeg (polyScale (zNat (Nat.succ n)) (hermiteRecurrencePoly n))) := by
  rfl

theorem hermiteRecurrencePoly_two :
    hermiteRecurrencePoly 2 = [zNeg zOne, zZero, zOne] := by
  rfl

theorem hermiteRecurrencePoly_three :
    hermiteRecurrencePoly 3 = [zZero, zNeg (zNat 3), zZero, zOne] := by
  rfl

theorem hermiteUnsignedCoefficient_matches_besselNumber (n k : Nat) :
    hermiteUnsignedCoefficient n k =
      BEDC.Derived.BesselNumberUp.besselNumber n k := by
  rfl

theorem hermiteUnsignedCoefficient_recurrence (n k : Nat) :
    hermiteUnsignedCoefficient (Nat.succ (Nat.succ n)) (Nat.succ k) =
      hermiteUnsignedCoefficient (Nat.succ n) (Nat.succ k) +
        Nat.succ n * hermiteUnsignedCoefficient n k := by
  exact BEDC.Derived.BesselNumberUp.besselNumber_recurrence n k

theorem hermiteSignedCoefficient_definition (n k : Nat) :
    hermiteSignedCoefficient n k =
      hermiteSignedNat k (BEDC.Derived.BesselNumberUp.besselNumber n k) := by
  rfl

theorem hermiteFactorialRatioMagnitude_definition (n k : Nat) :
    hermiteFactorialRatioMagnitude n k =
      BEDC.Derived.StirlingFirstUp.factorialNat n /
        ((2 ^ k) * BEDC.Derived.StirlingFirstUp.factorialNat k *
          BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k))) := by
  exact BEDC.Derived.BesselNumberUp.besselClosedFormula_definition n k

theorem hermiteFactorialRatioCoefficient_definition (n k : Nat) :
    hermiteFactorialRatioCoefficient n k =
      hermiteSignedNat k
        (BEDC.Derived.StirlingFirstUp.factorialNat n /
          ((2 ^ k) * BEDC.Derived.StirlingFirstUp.factorialNat k *
            BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k)))) := by
  unfold hermiteFactorialRatioCoefficient hermiteFactorialRatioMagnitude
  rw [BEDC.Derived.BesselNumberUp.besselClosedFormula_definition n k]

theorem hermiteExplicitTerm_definition (n k : Nat) :
    hermiteExplicitTerm n k =
      hermiteMonomial (n - (k + k))
        (hermiteSignedNat k
          (BEDC.Derived.StirlingFirstUp.factorialNat n /
            ((2 ^ k) * BEDC.Derived.StirlingFirstUp.factorialNat k *
              BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k))))) := by
  unfold hermiteExplicitTerm hermiteFactorialRatioCoefficient hermiteFactorialRatioMagnitude
  rw [BEDC.Derived.BesselNumberUp.besselClosedFormula_definition n k]

theorem hermiteExplicitPoly_zero :
    hermiteExplicitPoly 0 = [zOne] := by
  rfl

theorem hermiteExplicitPoly_one :
    hermiteExplicitPoly 1 = [zZero, zOne] := by
  rfl

theorem hermiteExplicitPoly_two :
    hermiteExplicitPoly 2 = [zNeg zOne, zZero, zOne] := by
  rfl

theorem hermiteExplicitPoly_three :
    hermiteExplicitPoly 3 = [zZero, zNeg (zNat 3), zZero, zOne] := by
  rfl

theorem hermiteCoefficient_zero_zero :
    hermiteSignedCoefficient 0 0 = zOne := by
  rfl

theorem hermiteCoefficient_one_linear :
    hermiteSignedCoefficient 1 0 = zOne := by
  rfl

theorem hermiteCoefficient_two_constant :
    hermiteSignedCoefficient 2 1 = zNeg zOne := by
  rfl

theorem hermiteCoefficient_three_linear :
    hermiteSignedCoefficient 3 1 = zNeg (zNat 3) := by
  rfl

theorem hermiteBesselRowSum_eq_involutionNumber (n : Nat) :
    BEDC.Derived.BesselNumberUp.besselRowSum n =
      BEDC.Derived.BesselNumberUp.involutionNumber n := by
  exact BEDC.Derived.BesselNumberUp.besselRowSum_eq_involutionNumber n

theorem gaussianMoment_zero :
    gaussianMoment 0 = 1 := by
  rfl

theorem gaussianMoment_one :
    gaussianMoment 1 = 0 := by
  rfl

theorem gaussianMoment_succ_succ (n : Nat) :
    gaussianMoment (Nat.succ (Nat.succ n)) =
      Nat.succ n * gaussianMoment n := by
  rfl

theorem hermiteOrthogonality_He0_He1_comb :
    BEDC.Derived.RationalUp.IntEq
      (hermiteGaussianInner (hermiteExplicitPoly 0) (hermiteExplicitPoly 1))
      zZero := by
  exact BEDC.Derived.RationalUp.IntEq_refl zZero

theorem hermiteOrthogonality_He0_He2_comb :
    BEDC.Derived.RationalUp.IntEq
      (hermiteGaussianInner (hermiteExplicitPoly 0) (hermiteExplicitPoly 2))
      zZero := by
  exact BEDC.Derived.RationalUp.IntEq_refl zZero

theorem hermiteOrthogonality_He1_He2_comb :
    BEDC.Derived.RationalUp.IntEq
      (hermiteGaussianInner (hermiteExplicitPoly 1) (hermiteExplicitPoly 2))
      zZero := by
  exact BEDC.Derived.RationalUp.IntEq_refl zZero

theorem hermiteBinomialBoundaryUsesExistingChoose (n : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n 0 = 1 := by
  exact BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n

end BEDC.Derived.HermitePolyUp
