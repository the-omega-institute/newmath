import BEDC.Derived.PolynomialUp.IntegerRing
import BEDC.Derived.MobiusInversionUp
import BEDC.Derived.DivisorFunctionUp

namespace BEDC.Derived.CyclotomicPolynomialUp

open BEDC.FKernel.Hist

abbrev IntegerUp := BEDC.Derived.PolynomialUp.IntegerUp
abbrev Poly := BEDC.Derived.PolynomialUp.Poly
abbrev PolyEq := BEDC.Derived.PolynomialUp.PolyEq

abbrev zZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

abbrev zOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

abbrev zNeg : IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntNeg

abbrev zEq : IntegerUp -> IntegerUp -> Prop :=
  BEDC.Derived.RationalUp.IntEq

private abbrev zLaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

private abbrev polyLaws :=
  BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws

def polyZero : Poly :=
  BEDC.Derived.PolynomialUp.polyZero

def polyOne : Poly :=
  BEDC.Derived.PolynomialUp.polyOne

def polyAdd : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyAdd

def polyNeg : Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyNeg

def polyMul : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyMul

def polyShift : Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyShift

def polyCoeff : Poly -> Nat -> IntegerUp :=
  BEDC.Derived.PolynomialUp.polyCoeff

def polySub (p q : Poly) : Poly :=
  polyAdd p (polyNeg q)

def xPolynomial : Poly :=
  [zZero, zOne]

def xMinusOne : Poly :=
  polySub xPolynomial polyOne

def xPower : Nat -> Poly
  | 0 => polyOne
  | Nat.succ n => polyShift (xPower n)

def xPowerMinusOne (n : Nat) : Poly :=
  polySub (xPower n) polyOne

def polyProduct : List Poly -> Poly
  | [] => polyOne
  | p :: ps => polyMul p (polyProduct ps)

def geometricSum : Nat -> Poly
  | 0 => polyZero
  | Nat.succ n => geometricSum n ++ [zOne]

def primeCyclotomicPolynomial (p : Nat) : Poly :=
  geometricSum p

def primeEulerPhiIndex : Nat -> Nat
  | 0 => 0
  | Nat.succ n => n

def mobiusExponentFromFactorEntries (entries : List BHist) : IntegerUp :=
  BEDC.Derived.ArithmeticFnUp.mobiusFactorsIntegerUp entries

def eulerPhiFromFactorEntries (entries : List BHist) : Nat :=
  BEDC.Derived.ArithmeticFnUp.eulerPhiFactorsNat entries

def IntegerCoefficientPolynomial (p : Poly) : Prop :=
  forall k : Nat, exists c : IntegerUp, zEq (polyCoeff p k) c

structure PolyDegreeCert (p : Poly) (degree : Nat) where
  lower : Poly
  shape : p = lower ++ [zOne]
  lower_length : lower.length = degree

structure BedcPrimeIndex (p : Nat) where
  witness : BHist
  witness_length : BEDC.FKernel.ExternalBinary.bwordLength witness = p
  witness_prime : BEDC.Derived.PrimeUp.NatPrime witness

structure CyclotomicRecursiveCertificate where
  phi : Nat -> Poly
  divisorRows : Nat -> List Nat
  factorEntries : Nat -> List BHist
  mobiusRows : Nat -> List (Nat × IntegerUp)
  eulerPhiRows : Nat -> Nat
  eulerPhiRows_read_factor_entries :
    forall n : Nat, eulerPhiRows n = eulerPhiFromFactorEntries (factorEntries n)
  divisor_product_eq_x_power_minus_one :
    forall n : Nat,
      PolyEq (polyProduct ((divisorRows n).map phi)) (xPowerMinusOne n)
  degree_certificates :
    forall n : Nat, PolyDegreeCert (phi n) (eulerPhiRows n)

structure CyclotomicMobiusQuotientRow where
  index : Nat
  target : Poly
  positiveFactors : List Poly
  negativeFactors : List Poly
  mobiusExponentRows : List (Nat × IntegerUp)
  quotient_identity :
    PolyEq (polyProduct positiveFactors) (polyMul target (polyProduct negativeFactors))

structure CyclotomicFactorizationPhiRow where
  index : Nat
  factorEntries : List BHist
  phiValue : Nat
  phiValue_reads_euler : phiValue = eulerPhiFromFactorEntries factorEntries

theorem xPower_zero :
    xPower 0 = polyOne := by
  rfl

theorem xPower_succ (n : Nat) :
    xPower (Nat.succ n) = polyShift (xPower n) := by
  rfl

theorem xPowerMinusOne_unfold (n : Nat) :
    xPowerMinusOne n = polySub (xPower n) polyOne := by
  rfl

theorem polyProduct_nil :
    polyProduct [] = polyOne := by
  rfl

theorem polyProduct_cons (p : Poly) (ps : List Poly) :
    polyProduct (p :: ps) = polyMul p (polyProduct ps) := by
  rfl

theorem geometricSum_zero :
    geometricSum 0 = polyZero := by
  rfl

theorem geometricSum_succ (n : Nat) :
    geometricSum (Nat.succ n) = geometricSum n ++ [zOne] := by
  rfl

private theorem list_length_append_singleton {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).length = Nat.succ xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons y ys ih =>
      change Nat.succ ((ys ++ [x]).length) = Nat.succ (Nat.succ ys.length)
      exact congrArg Nat.succ ih

theorem geometricSum_length :
    forall n : Nat, (geometricSum n).length = n
  | 0 => by
      rfl
  | Nat.succ n => by
      change (geometricSum n ++ [zOne]).length = Nat.succ n
      exact Eq.trans
        (list_length_append_singleton (geometricSum n) zOne)
        (congrArg Nat.succ (geometricSum_length n))

def geometricSum_degree_cert (n : Nat) :
    PolyDegreeCert (geometricSum (Nat.succ n)) n := by
  exact {
    lower := geometricSum n
    shape := rfl
    lower_length := geometricSum_length n
  }

theorem primeEulerPhiIndex_succ (n : Nat) :
    primeEulerPhiIndex (Nat.succ n) = n := by
  rfl

theorem primeCyclotomicPolynomial_formula (p : Nat) :
    primeCyclotomicPolynomial p = geometricSum p := by
  rfl

theorem primeCyclotomicPolynomial_formula_for_bedc_prime
    {p : Nat} (_prime : BedcPrimeIndex p) :
    primeCyclotomicPolynomial p = geometricSum p := by
  rfl

def primeCyclotomicPolynomial_degree_phi_index (n : Nat) :
    PolyDegreeCert
      (primeCyclotomicPolynomial (Nat.succ n))
      (primeEulerPhiIndex (Nat.succ n)) := by
  exact geometricSum_degree_cert n

theorem eulerPhiFromFactorEntries_singleton (entry : BHist) :
    eulerPhiFromFactorEntries [entry] =
      BEDC.FKernel.ExternalBinary.bwordLength entry - 1 := by
  unfold eulerPhiFromFactorEntries
  change (BEDC.FKernel.ExternalBinary.bwordLength entry - 1) * 1 =
    BEDC.FKernel.ExternalBinary.bwordLength entry - 1
  exact Nat.mul_one (BEDC.FKernel.ExternalBinary.bwordLength entry - 1)

theorem bedcPrimeIndex_single_factor_euler_phi
    {p : Nat} (prime : BedcPrimeIndex p) :
    eulerPhiFromFactorEntries [prime.witness] = primeEulerPhiIndex p := by
  exact Eq.trans
    (eulerPhiFromFactorEntries_singleton prime.witness)
    (Eq.trans (congrArg (fun n => n - 1) prime.witness_length) (by
      cases p with
      | zero =>
          rfl
      | succ n =>
          rfl))

def primeCyclotomicPolynomial_degree_euler_phi_for_bedc_prime
    {n : Nat} (prime : BedcPrimeIndex (Nat.succ n)) :
    PolyDegreeCert
      (primeCyclotomicPolynomial (Nat.succ n))
      (eulerPhiFromFactorEntries [prime.witness]) := by
  rw [bedcPrimeIndex_single_factor_euler_phi prime]
  exact primeCyclotomicPolynomial_degree_phi_index n

theorem integerCoefficientPolynomial_all (p : Poly) :
    IntegerCoefficientPolynomial p := by
  intro k
  exact Exists.intro (polyCoeff p k) (zLaws.eq_refl (polyCoeff p k))

theorem primeCyclotomicPolynomial_integer_coefficients (p : Nat) :
    IntegerCoefficientPolynomial (primeCyclotomicPolynomial p) := by
  exact integerCoefficientPolynomial_all (primeCyclotomicPolynomial p)

theorem cyclotomic_certificate_integer_coefficients
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    IntegerCoefficientPolynomial (cert.phi n) := by
  exact integerCoefficientPolynomial_all (cert.phi n)

def certifiedCyclotomicPolynomial
    (cert : CyclotomicRecursiveCertificate) (n : Nat) : Poly :=
  cert.phi n

def certifiedCyclotomicDivisorRows
    (cert : CyclotomicRecursiveCertificate) (n : Nat) : List Nat :=
  cert.divisorRows n

def certifiedCyclotomicEulerPhiRow
    (cert : CyclotomicRecursiveCertificate) (n : Nat) : Nat :=
  cert.eulerPhiRows n

theorem cyclotomic_recursive_x_power_minus_one_product
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    PolyEq (polyProduct ((cert.divisorRows n).map cert.phi)) (xPowerMinusOne n) := by
  exact cert.divisor_product_eq_x_power_minus_one n

theorem certifiedCyclotomicPolynomial_divisor_product_eq_x_power_minus_one
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    PolyEq
      (polyProduct
        ((certifiedCyclotomicDivisorRows cert n).map
          (certifiedCyclotomicPolynomial cert)))
      (xPowerMinusOne n) := by
  exact cert.divisor_product_eq_x_power_minus_one n

def cyclotomic_recursive_degree_phi_certificate
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    PolyDegreeCert (cert.phi n) (cert.eulerPhiRows n) := by
  exact cert.degree_certificates n

theorem cyclotomic_recursive_euler_phi_reads_factor_entries
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    cert.eulerPhiRows n = eulerPhiFromFactorEntries (cert.factorEntries n) := by
  exact cert.eulerPhiRows_read_factor_entries n

def certifiedCyclotomicPolynomial_degree_euler_phi
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    PolyDegreeCert
      (certifiedCyclotomicPolynomial cert n)
      (certifiedCyclotomicEulerPhiRow cert n) := by
  exact cert.degree_certificates n

def certifiedCyclotomicPolynomial_degree_euler_phi_from_factor_entries
    (cert : CyclotomicRecursiveCertificate) (n : Nat) :
    PolyDegreeCert
      (certifiedCyclotomicPolynomial cert n)
      (eulerPhiFromFactorEntries (cert.factorEntries n)) := by
  rw [← cert.eulerPhiRows_read_factor_entries n]
  exact cert.degree_certificates n

theorem cyclotomic_mobius_quotient_identity
    (row : CyclotomicMobiusQuotientRow) :
    PolyEq (polyProduct row.positiveFactors)
      (polyMul row.target (polyProduct row.negativeFactors)) := by
  exact row.quotient_identity

theorem cyclotomic_factorization_phi_reads_euler
    (row : CyclotomicFactorizationPhiRow) :
    row.phiValue = eulerPhiFromFactorEntries row.factorEntries := by
  exact row.phiValue_reads_euler

theorem mobiusExponentFromFactorEntries_unfold (entries : List BHist) :
    mobiusExponentFromFactorEntries entries =
      BEDC.Derived.ArithmeticFnUp.mobiusFactorsIntegerUp entries := by
  rfl

theorem eulerPhiFromFactorEntries_unfold (entries : List BHist) :
    eulerPhiFromFactorEntries entries =
      BEDC.Derived.ArithmeticFnUp.eulerPhiFactorsNat entries := by
  rfl

end BEDC.Derived.CyclotomicPolynomialUp
