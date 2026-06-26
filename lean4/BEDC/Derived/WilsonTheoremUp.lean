import BEDC.Derived.FactorialResidueProduct
import BEDC.Derived.WilsonUp

namespace BEDC.Derived.WilsonTheoremUp

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.WilsonUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

def wilsonResiduesAscending {p : BHist} (prime : NatPrime p) : List (ZMod p) :=
  nonzeroResiduesAscending prime

theorem wilson_prime_two :
    zmodEq (wilsonFactorialResidue NatPrime_first_pair.left)
      (zmodMinusOne NatPrime_first_pair.left) := by
  rfl

theorem wilson_prime_three :
    zmodEq (wilsonFactorialResidue NatPrime_first_pair.right)
      (zmodMinusOne NatPrime_first_pair.right) := by
  rfl

theorem wilson_residues_product_factorial {p : BHist}
    (prime : NatPrime p) :
    zmodEq
      (wilsonFactorialResidue prime)
      (listProd (zmodRelCommRing prime) (wilsonResiduesAscending prime)) := by
  exact zmodEq_symm
    (zmod_nonzeroResiduesAscending_prod_eq_factorial_mod prime)

theorem wilson_from_standard_inverse_pairing {p : BHist}
    (prime : NatPrime p)
    (pairSeeds : List (NonzeroResidue p))
    (paired :
      ListPerm (wilsonResiduesAscending prime)
        ([zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime] ++
          inversePairFactors prime pairSeeds)) :
    zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) := by
  exact wilson_from_standard_pairing prime
    { residues := wilsonResiduesAscending prime
      pairSeeds := pairSeeds
      paired_residue_permutation := paired
      factorial_product := wilson_residues_product_factorial prime }

theorem wilson_from_standard_pairing_data {p : BHist}
    (prime : NatPrime p)
    (data : WilsonStandardPairingData p prime) :
    zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) := by
  exact wilson_from_standard_pairing prime data

end BEDC.Derived.WilsonTheoremUp
