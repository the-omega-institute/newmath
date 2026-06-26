import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Spine.FiniteData
import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.CRTUp
import BEDC.Derived.MobiusInversionUp
import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.ZModResidueList

namespace BEDC.Algebra.Spine.NumberTheorySpectra

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.CRTUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

abbrev Hist := BHist
abbrev NatDivides := BEDC.Derived.PrimeUp.NatDivides
abbrev NatPrime := BEDC.Derived.PrimeUp.NatPrime
abbrev PrimeUp (p : Hist) := NatPrime p
abbrev VpRel (p n k : Hist) := IsPadicValNat p n k
abbrev DirichletFunction := BEDC.Derived.MobiusInversionUp.ArithmeticFunction

private theorem listContainsPrime_of_mem {p : Hist} :
    ∀ {xs : List Hist}, p ∈ xs -> listContainsPrime p xs = true
  | [], member => by
      cases member
  | q :: qs, member => by
      unfold listContainsPrime
      cases member with
      | head =>
          rw [if_pos rfl]
      | tail _ tailMember =>
          by_cases same : p = q
          · rw [if_pos same]
          · rw [if_neg same]
            exact listContainsPrime_of_mem tailMember

private theorem primeFactorizationProduct_factor_prime {p : Hist} :
    ∀ {factors : List Hist} {n : Hist},
      PrimeFactorizationProduct factors n -> p ∈ factors -> NatPrime p
  | [], _n, _product, member => by
      cases member
  | q :: qs, n, product, member => by
      change NatPrime q ∧ ∃ tailProduct : Hist,
        PrimeFactorizationProduct qs tailProduct ∧ NatMul q tailProduct n at product
      cases product with
      | intro qPrime tail =>
          cases member with
          | head =>
              exact qPrime
          | tail _ tailMember =>
              cases tail with
              | intro tailProduct tailData =>
                  exact primeFactorizationProduct_factor_prime tailData.left tailMember

structure FactorizationLedger (n : Hist) where
  factors : List Hist
  all_prime : ∀ p : Hist, p ∈ factors -> NatPrime p
  product_rel : PrimeFactorizationProduct factors n

namespace FactorizationLedger

theorem result_unary {n : Hist} (ledger : FactorizationLedger n) :
    UnaryHistory n :=
  PrimeFactorizationProduct_result_unary ledger.product_rel

theorem result_not_empty {n : Hist} (ledger : FactorizationLedger n) :
    hsame n BHist.Empty -> False :=
  PrimeFactorizationProduct_result_not_empty ledger.product_rel

theorem factor_prime {n p : Hist} (ledger : FactorizationLedger n) :
    p ∈ ledger.factors -> NatPrime p := by
  intro member
  exact ledger.all_prime p member

theorem factor_divides {n p : Hist} (ledger : FactorizationLedger n) :
    p ∈ ledger.factors -> NatDivides p n := by
  intro member
  exact listContainsPrime_product_divides
    (listContainsPrime_of_mem member) ledger.product_rel

theorem perm_unique {n : Hist} (left right : FactorizationLedger n) :
    ListPermPrime left.factors right.factors :=
  factorization_unique_perm left.product_rel right.product_rel

theorem prime_power_readout {n p : Hist} (ledger : FactorizationLedger n)
    (prime : NatPrime p) :
    VpRel p n (primeCount p ledger.factors) :=
  primeCount_is_valuation ledger.product_rel prime

theorem prime_power_readout_unique {n p k : Hist} (ledger : FactorizationLedger n)
    (prime : NatPrime p) :
    VpRel p n k -> hsame (primeCount p ledger.factors) k := by
  intro valuation
  exact primeCount_eq_valuation ledger.product_rel prime valuation

theorem reconstructs {n : Hist} (ledger : FactorizationLedger n) :
    hsame (primePowerProduct ledger.factors) n :=
  primePowerProduct_eq_flat ledger.product_rel

end FactorizationLedger

theorem factorization_ledger_exists {n : Hist}
    (large : NatUnaryStrictPrefix NatOne n) :
    ∃ ledger : FactorizationLedger n, PrimeFactorization n ledger.factors := by
  cases product_formula_nat n large with
  | intro entries factorization =>
      exact ⟨{
        factors := entries
        all_prime := by
          intro p member
          exact primeFactorizationProduct_factor_prime factorization.right member
        product_rel := factorization.right
      }, factorization⟩

theorem factorization_ledgers_perm_unique {n : Hist}
    (left right : FactorizationLedger n) :
    ListPermPrime left.factors right.factors :=
  FactorizationLedger.perm_unique left right

structure PrimeCoordinateReadout (n : Hist) where
  ledger : FactorizationLedger n
  support : List Hist
  support_perm : ListPermPrime support ledger.factors
  coord : Hist -> Hist
  coord_spec : ∀ p : Hist, NatPrime p -> VpRel p n (coord p)
  reconstruction : hsame (primePowerProduct support) n

namespace PrimeCoordinateReadout

def fromLedger {n : Hist} (ledger : FactorizationLedger n) :
    PrimeCoordinateReadout n where
  ledger := ledger
  support := ledger.factors
  support_perm := List.Perm.refl ledger.factors
  coord := fun p => primeCount p ledger.factors
  coord_spec := by
    intro p prime
    exact ledger.prime_power_readout prime
  reconstruction := ledger.reconstructs

theorem coordinate_unique {n p k : Hist} (readout : PrimeCoordinateReadout n)
    (prime : NatPrime p) :
    VpRel p n k -> hsame (readout.coord p) k := by
  intro valuation
  exact IsPadicValNat_unique (readout.coord_spec p prime) valuation

theorem support_product_reconstructs {n : Hist} (readout : PrimeCoordinateReadout n) :
    hsame (primePowerProduct readout.support) n :=
  readout.reconstruction

end PrimeCoordinateReadout

structure VpMulAddCertificate (p m n mn a b c : Hist) where
  prime : NatPrime p
  left : VpRel p m a
  right : VpRel p n b
  product : NatMul m n mn
  add : NatAdd a b c

theorem vp_mul_add {p m n mn a b c : Hist} :
    VpMulAddCertificate p m n mn a b c -> VpRel p mn c := by
  intro cert
  exact IsPadicValNat_mul_add_exact_of_prime cert.prime cert.left cert.right
    cert.add cert.product

structure ResidueSpectrumUp (m : Hist) where
  modulus_unary : UnaryHistory m
  modulus_nonempty : hsame m BHist.Empty -> False
  classes : List (ZMod m)
  complete : ∀ x : ZMod m, x ∈ classes
  separated : ListNoDup classes

namespace ResidueSpectrumUp

theorem class_val_unary {m : Hist} (spectrum : ResidueSpectrumUp m)
    (x : ZMod m) :
    UnaryHistory x.val :=
  zmodVal_unary spectrum.modulus_unary x

theorem contains {m : Hist} (spectrum : ResidueSpectrumUp m)
    (x : ZMod m) :
    x ∈ spectrum.classes :=
  spectrum.complete x

theorem eq_of_zmodEq {m : Hist} {x y : ZMod m} :
    zmodEq x y -> x = y :=
  BEDC.Derived.ZModResidueList.zmod_ext

end ResidueSpectrumUp

structure ResiduePairSpectrum (m n : Hist) where
  left : ResidueSpectrumUp m
  right : ResidueSpectrumUp n
  coprime : NatGcd m n NatOne

def residueProductModulus (m n : Hist) : Hist :=
  crtModulus m n

theorem residue_product_left_divides {m n : Hist}
    (left : UnaryHistory m) (right : UnaryHistory n) :
    NatDivides m (residueProductModulus m n) :=
  crtModulus_left_divides left right

theorem residue_product_right_divides {m n : Hist}
    (left : UnaryHistory m) (right : UnaryHistory n) :
    NatDivides n (residueProductModulus m n) :=
  crtModulus_right_divides left right

structure FinitePrimeWindow where
  primes : List Hist
  all_prime : ∀ p : Hist, p ∈ primes -> NatPrime p
  nodup : ListNoDup primes

namespace FinitePrimeWindow

def contains (window : FinitePrimeWindow) (p : Hist) : Prop :=
  p ∈ window.primes

theorem member_prime (window : FinitePrimeWindow) {p : Hist} :
    window.contains p -> NatPrime p :=
  window.all_prime p

def asNatWindow (window : BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow) :
    List Nat :=
  window.elems

end FinitePrimeWindow

structure PrimeWindowSpectrum (window : FinitePrimeWindow) where
  source : Hist
  readout : PrimeCoordinateReadout source
  window_sound :
    ∀ p : Hist, window.contains p -> VpRel p source (readout.coord p)

namespace PrimeWindowSpectrum

theorem readout_prime_coordinate {window : FinitePrimeWindow}
    (spectrum : PrimeWindowSpectrum window) {p : Hist} :
    window.contains p -> VpRel p spectrum.source (spectrum.readout.coord p) :=
  spectrum.window_sound p

end PrimeWindowSpectrum

structure ArithmeticFunctionUp where
  value : DirichletFunction

namespace ArithmeticFunctionUp

def ofFunction (f : DirichletFunction) : ArithmeticFunctionUp where
  value := f

def one : ArithmeticFunctionUp :=
  ofFunction oneFunction

def epsilon : ArithmeticFunctionUp :=
  ofFunction epsilonFunction

def mobius : ArithmeticFunctionUp :=
  ofFunction mobiusFunction

def DirichletConvolution (f g : ArithmeticFunctionUp) : ArithmeticFunctionUp :=
  ofFunction (dirichletConvolution f.value g.value)

theorem extensional_eq_refl (f : ArithmeticFunctionUp) :
    ArithmeticFnEq f.value f.value := by
  intro entries
  exact IntEq_refl (f.value entries)

theorem dirichlet_convolution_left_congr {f f' g : ArithmeticFunctionUp} :
    ArithmeticFnEq f.value f'.value ->
      ArithmeticFnEq (DirichletConvolution f g).value
        (DirichletConvolution f' g).value := by
  intro same
  exact dirichletConvolution_left_congr same

theorem dirichlet_convolution_right_congr {f g g' : ArithmeticFunctionUp} :
    ArithmeticFnEq g.value g'.value ->
      ArithmeticFnEq (DirichletConvolution f g).value
        (DirichletConvolution f g').value := by
  intro same
  exact dirichletConvolution_right_congr same

theorem mobius_left_unit :
    ArithmeticFnEq (DirichletConvolution mobius one).value epsilon.value :=
  mobiusDirichletUnit

theorem mobius_inversion {f g : ArithmeticFunctionUp}
    (zetaRelation :
      ArithmeticFnEq g.value (DirichletConvolution f one).value)
    (convolutionAssoc :
      ArithmeticFnEq
        (DirichletConvolution mobius (DirichletConvolution f one)).value
        (DirichletConvolution (DirichletConvolution mobius one) f).value)
    (epsilonLeft :
      ArithmeticFnEq (DirichletConvolution epsilon f).value f.value) :
    ArithmeticFnEq (DirichletConvolution mobius g).value f.value :=
  BEDC.Derived.MobiusInversionUp.mobiusInversion f.value g.value
    zetaRelation convolutionAssoc epsilonLeft

end ArithmeticFunctionUp

structure ArithmeticFunctionSpectrum (n : Hist) where
  ledger : FactorizationLedger n
  phi : Hist
  sigma : Hist
  mu : _root_.Int
  phi_spec : EulerPhiOfFactorization n phi
  sigma_spec : DivisorSigmaOfFactorization n sigma
  mu_spec : MobiusOfFactorization n mu

def arithmeticSpectrumFromLedger {n : Hist}
    (ledger : FactorizationLedger n) : ArithmeticFunctionSpectrum n where
  ledger := ledger
  phi := eulerPhiFactors ledger.factors
  sigma := sigmaFactors ledger.factors
  mu := mobiusFactorsInt ledger.factors
  phi_spec := ⟨ledger.factors, ⟨ledger.result_unary, ledger.product_rel⟩, hsame_refl _⟩
  sigma_spec := ⟨ledger.factors, ⟨ledger.result_unary, ledger.product_rel⟩, hsame_refl _⟩
  mu_spec := ⟨ledger.factors, ⟨ledger.result_unary, ledger.product_rel⟩, rfl⟩

theorem arithmetic_phi_unary {n : Hist} (spectrum : ArithmeticFunctionSpectrum n) :
    UnaryHistory spectrum.phi := by
  cases spectrum.phi_spec with
  | intro entries data =>
      exact unary_transport (eulerPhiFactors_unary entries) (hsame_symm data.right)

theorem arithmetic_sigma_unary {n : Hist} (spectrum : ArithmeticFunctionSpectrum n) :
    UnaryHistory spectrum.sigma := by
  cases spectrum.sigma_spec with
  | intro entries data =>
      exact unary_transport (sigmaFactors_unary entries) (hsame_symm data.right)

theorem euler_phi_coprime_product {m n mn : Hist} {xs ys : List Hist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            EulerPhiOfFactorization mn
              (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) :=
  eulerPhi_factorization_product_multiplicative_of_gcd_one

end BEDC.Algebra.Spine.NumberTheorySpectra
