import BEDC.Derived.PadicValuationUp

namespace BEDC.Derived.PrimeAdicLocalSlicing

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicValuationUp

structure PrimeAdicSlice (n : BHist) where
  prime : BHist
  exponent : BHist
  prime_row : NatPrime prime
  valuation : padicValuationNat prime n exponent

structure PrimeAdicSliceSupport (entries : List BHist) where
  primes : List BHist
  nodup : primes.Nodup
  covers_entries : ∀ p : BHist, p ∈ entries -> p ∈ primes
  from_entries : ∀ p : BHist, p ∈ primes -> p ∈ entries

def primeAdicSliceOfFactor (n p : BHist) (entries : List BHist)
    (product : PrimeFactorizationProduct entries n) (prime : NatPrime p) :
    PrimeAdicSlice n where
  prime := p
  exponent := primeCount p entries
  prime_row := prime
  valuation := padicValuationNat_prime_factor_count product prime

private theorem primeFactorizationProduct_factor_prime {p : BHist} :
    ∀ {entries : List BHist} {n : BHist},
      PrimeFactorizationProduct entries n -> p ∈ entries -> NatPrime p
  | [], _n, _product, member => by
      cases member
  | q :: qs, n, product, member => by
      change NatPrime q ∧ ∃ tailProduct : BHist,
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

private def primeAdicSlicesFromMembers (n : BHist) (entries : List BHist)
    (product : PrimeFactorizationProduct entries n) :
    ∀ support : List BHist,
      (∀ p : BHist, p ∈ support -> p ∈ entries) -> List (PrimeAdicSlice n)
  | [], _support_subset => []
  | p :: ps, support_subset =>
      primeAdicSliceOfFactor n p entries product
        (primeFactorizationProduct_factor_prime product
          (support_subset p (List.Mem.head ps))) ::
        primeAdicSlicesFromMembers n entries product ps
          (fun q qMem => support_subset q (List.Mem.tail p qMem))

def primeAdicSlices (n : BHist) (entries : List BHist)
    (product : PrimeFactorizationProduct entries n) : List (PrimeAdicSlice n) :=
  primeAdicSlicesFromMembers n entries product entries (fun _ member => member)

def primeAdicSlicesOnSupport (n : BHist) (entries : List BHist)
    (product : PrimeFactorizationProduct entries n)
    (support : PrimeAdicSliceSupport entries) : List (PrimeAdicSlice n) :=
  primeAdicSlicesFromMembers n entries product support.primes support.from_entries

theorem primeAdicSliceSupport_nodup {entries : List BHist}
    (support : PrimeAdicSliceSupport entries) :
    support.primes.Nodup :=
  support.nodup

theorem primeAdicSlice_exponent_unary {n : BHist}
    (slice : PrimeAdicSlice n) :
    UnaryHistory slice.exponent :=
  (PDvdNat_power_unary slice.valuation.left).right

theorem primeAdicSlice_locality {n p k : BHist}
    (slice : PrimeAdicSlice n) :
    hsame slice.prime p -> hsame slice.exponent k ->
      padicValuationNat p n k := by
  intro samePrime sameExponent
  cases samePrime
  cases sameExponent
  exact slice.valuation

theorem primeAdicSlice_unique_exponent {n p k : BHist}
    (slice : PrimeAdicSlice n) :
    hsame slice.prime p -> padicValuationNat p n k ->
      hsame slice.exponent k := by
  intro samePrime valuation
  cases samePrime
  exact padicValuationNat_unique slice.valuation valuation

theorem primeAdicSlice_power_divides {n : BHist}
    (slice : PrimeAdicSlice n) :
    padicPrimePowerDividesNat slice.prime slice.exponent n :=
  padicValuationNat_divides slice.valuation

theorem primeAdicSlices_reconstruct {n : BHist} {entries : List BHist} :
    PrimeFactorizationProduct entries n ->
      hsame (primePowerProduct entries) n := by
  intro product
  exact primePowerProduct_eq_flat product

theorem primeAdicSlices_coordinate {n p : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n) (prime : NatPrime p) :
    padicValuationNat p n (primeCount p entries) := by
  exact padicValuationNat_prime_factor_count product prime

theorem primeAdicSlices_coordinate_unique {n p k : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n) (prime : NatPrime p) :
    padicValuationNat p n k -> hsame (primeCount p entries) k := by
  intro valuation
  exact padicValuationNat_prime_factor_count_unique product prime valuation

theorem primeAdicSlicesOnSupport_coordinate {n : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n)
    (support : PrimeAdicSliceSupport entries) :
    ∀ p : BHist, p ∈ support.primes ->
      padicValuationNat p n (primeCount p entries) := by
  intro p member
  exact padicValuationNat_prime_factor_count product
    (primeFactorizationProduct_factor_prime product
      (support.from_entries p member))

theorem primeAdicSlicesOnSupport_entry_coordinate {n : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n)
    (support : PrimeAdicSliceSupport entries) :
    ∀ p : BHist, p ∈ entries ->
      padicValuationNat p n (primeCount p entries) := by
  intro p member
  exact primeAdicSlicesOnSupport_coordinate product support p
    (support.covers_entries p member)

theorem primeAdicSlices_local_to_global {n : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n) :
    (∀ p : BHist, p ∈ entries ->
      padicValuationNat p n (primeCount p entries)) ∧
        hsame (primePowerProduct entries) n := by
  constructor
  · intro p member
    exact padicValuationNat_prime_factor_count product
      (primeFactorizationProduct_factor_prime product member)
  · exact primeAdicSlices_reconstruct product

theorem primeAdicSlicesOnSupport_local_to_global {n : BHist} {entries : List BHist}
    (product : PrimeFactorizationProduct entries n)
    (support : PrimeAdicSliceSupport entries) :
    support.primes.Nodup ∧
      (∀ p : BHist, p ∈ support.primes ->
        padicValuationNat p n (primeCount p entries)) ∧
        hsame (primePowerProduct entries) n := by
  constructor
  · exact support.nodup
  · constructor
    · exact primeAdicSlicesOnSupport_coordinate product support
    · exact primeAdicSlices_reconstruct product

end BEDC.Derived.PrimeAdicLocalSlicing
