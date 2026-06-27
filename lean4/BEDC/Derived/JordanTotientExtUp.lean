import BEDC.Derived.DedekindPsiUp
import BEDC.Derived.DirichletRingUp
import BEDC.Derived.JordanTotientUp

namespace BEDC.Derived.JordanTotientExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.JordanTotientUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp

abbrev ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.ArithmeticFunction

def natValueIntegerUp (n : Nat) : IntegerUp :=
  intOfNat (natToUnary n) (natToUnary_unary n)

def idPowerFunction (k : Nat) : ArithmeticFunction :=
  fun entries => natValueIntegerUp (natPow (primeFlatProductNat entries) k)

def jordanTotientFunction (k : Nat) : ArithmeticFunction :=
  fun entries => natValueIntegerUp (jordanTotientFactorsNat k entries)

def divisorSigmaPowerFunction (k : Nat) : ArithmeticFunction :=
  fun entries =>
    natValueIntegerUp
      (divisorPowerSumNat k (divisorProductsOfFactorization entries))

def jordanTotientZetaRelation (k : Nat) : Prop :=
  ArithmeticFnEq (idPowerFunction k)
    (dirichletConvolution (jordanTotientFunction k) oneFunction)

def divisorSigmaZetaRelation (k : Nat) : Prop :=
  ArithmeticFnEq (divisorSigmaPowerFunction k)
    (dirichletConvolution (idPowerFunction k) oneFunction)

def jordanTotientMobiusConvolutionAssoc (k : Nat) : Prop :=
  ArithmeticFnEq
    (dirichletConvolution mobiusFunction
      (dirichletConvolution (jordanTotientFunction k) oneFunction))
    (dirichletConvolution
      (dirichletConvolution mobiusFunction oneFunction)
      (jordanTotientFunction k))

def idPowerMobiusConvolutionAssoc (k : Nat) : Prop :=
  ArithmeticFnEq
    (dirichletConvolution mobiusFunction
      (dirichletConvolution (idPowerFunction k) oneFunction))
    (dirichletConvolution
      (dirichletConvolution mobiusFunction oneFunction)
      (idPowerFunction k))

def jordanTotientEpsilonLeft (k : Nat) : Prop :=
  ArithmeticFnEq
    (dirichletConvolution epsilonFunction (jordanTotientFunction k))
    (jordanTotientFunction k)

def idPowerEpsilonLeft (k : Nat) : Prop :=
  ArithmeticFnEq
    (dirichletConvolution epsilonFunction (idPowerFunction k))
    (idPowerFunction k)

theorem jordanTotient_eq_mobius_mul_idPower_dirichlet
    (k : Nat)
    (zetaRelation : jordanTotientZetaRelation k)
    (convolutionAssoc : jordanTotientMobiusConvolutionAssoc k)
    (epsilonLeft : jordanTotientEpsilonLeft k) :
    ArithmeticFnEq
      (dirichletConvolution mobiusFunction (idPowerFunction k))
      (jordanTotientFunction k) := by
  exact mobiusInversion (jordanTotientFunction k) (idPowerFunction k)
    zetaRelation convolutionAssoc epsilonLeft

theorem idPower_eq_mobius_mul_sigma_dirichlet
    (k : Nat)
    (zetaRelation : divisorSigmaZetaRelation k)
    (convolutionAssoc : idPowerMobiusConvolutionAssoc k)
    (epsilonLeft : idPowerEpsilonLeft k) :
    ArithmeticFnEq
      (dirichletConvolution mobiusFunction (divisorSigmaPowerFunction k))
      (idPowerFunction k) := by
  exact mobiusInversion (idPowerFunction k) (divisorSigmaPowerFunction k)
    zetaRelation convolutionAssoc epsilonLeft

theorem jordanTotient_eq_double_mobius_mul_sigma_dirichlet
    (k : Nat)
    (jordanZeta : jordanTotientZetaRelation k)
    (jordanAssoc : jordanTotientMobiusConvolutionAssoc k)
    (jordanEpsilon : jordanTotientEpsilonLeft k)
    (sigmaZeta : divisorSigmaZetaRelation k)
    (sigmaAssoc : idPowerMobiusConvolutionAssoc k)
    (sigmaEpsilon : idPowerEpsilonLeft k) :
    ArithmeticFnEq
      (dirichletConvolution mobiusFunction
        (dirichletConvolution mobiusFunction (divisorSigmaPowerFunction k)))
      (jordanTotientFunction k) := by
  have sigmaToId :
      ArithmeticFnEq
        (dirichletConvolution mobiusFunction (divisorSigmaPowerFunction k))
        (idPowerFunction k) :=
    idPower_eq_mobius_mul_sigma_dirichlet k
      sigmaZeta sigmaAssoc sigmaEpsilon
  have lift :
      ArithmeticFnEq
        (dirichletConvolution mobiusFunction
          (dirichletConvolution mobiusFunction (divisorSigmaPowerFunction k)))
        (dirichletConvolution mobiusFunction (idPowerFunction k)) :=
    dirichletConvolution_right_congr sigmaToId
  intro entries
  exact IntEq_trans (lift entries)
    ((jordanTotient_eq_mobius_mul_idPower_dirichlet k
      jordanZeta jordanAssoc jordanEpsilon) entries)

def jordanTotientProfileDirichletSumNat
    (k : Nat) (profile : PrimePowerProfile) : Nat :=
  jordanTotientProfileDivisorSumNat k profile

def jordanTotientProfileIdPowerNat
    (k : Nat) (profile : PrimePowerProfile) : Nat :=
  natPow (primeFlatProductNat (expandProfile profile)) k

theorem jordanTotient_profile_dirichlet_sum_eq_idPower_nat
    (k : Nat) {profile : PrimePowerProfile} :
    ProfileValid profile ->
      jordanTotientProfileDirichletSumNat k profile =
        jordanTotientProfileIdPowerNat k profile := by
  intro valid
  exact jordanTotient_profile_divisor_sum_nat k valid

def jordanTotientProfileDirichletSum
    (k : Nat) (profile : PrimePowerProfile) : BHist :=
  natToUnary (jordanTotientProfileDirichletSumNat k profile)

def jordanTotientProfileIdPower
    (k : Nat) (profile : PrimePowerProfile) : BHist :=
  natToUnary (jordanTotientProfileIdPowerNat k profile)

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr
    lengthEq

theorem jordanTotient_profile_dirichlet_sum_eq_idPower
    (k : Nat) {profile : PrimePowerProfile} :
    ProfileValid profile ->
      hsame (jordanTotientProfileDirichletSum k profile)
        (jordanTotientProfileIdPower k profile) := by
  intro valid
  apply unary_hsame_of_length
  · unfold jordanTotientProfileDirichletSum
    exact natToUnary_unary _
  · unfold jordanTotientProfileIdPower
    exact natToUnary_unary _
  · unfold jordanTotientProfileDirichletSum jordanTotientProfileIdPower
    rw [natToUnary_length, natToUnary_length]
    exact jordanTotient_profile_dirichlet_sum_eq_idPower_nat k valid

theorem jordanTotient_sum_eq_idPower_of_profile_factorization
    (k : Nat) {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile ->
      PrimeFactorization n (expandProfile profile) ->
        hsame (jordanTotientProfileDirichletSum k profile)
          (natToUnary (natPow (bwordLength n) k)) := by
  intro valid factorization
  change hsame (jordanTotientProfileDivisorSum k profile)
    (natToUnary (natPow (bwordLength n) k))
  exact jordanTotient_divisor_sum_of_profile k valid factorization

theorem jordanTotient_one_recovers_phi_dirichlet_profile
    {profile : PrimePowerProfile} :
    ProfileValid profile ->
      hsame (jordanTotientProfileDirichletSum 1 profile)
        (jordanTotientProfileIdPower 1 profile) := by
  intro valid
  exact jordanTotient_profile_dirichlet_sum_eq_idPower 1 valid

end BEDC.Derived.JordanTotientExtUp
