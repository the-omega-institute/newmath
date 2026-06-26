import BEDC.Algebra.FiniteFold
import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.ZModFieldUp

namespace BEDC.Derived.WilsonUp

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FactorialUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModUp
open BEDC.Derived.EulerTheoremUp

def primePred : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 tail => tail

theorem primePred_unary {p : BHist} (prime : NatPrime p) :
    UnaryHistory (primePred p) := by
  cases p with
  | Empty =>
      exact False.elim ((NatPrime_empty_absurd prime) rfl)
  | e0 tail =>
      cases prime.left
  | e1 tail =>
      exact unary_e1_inversion prime.left

def wilsonFactorialResidue {p : BHist} (prime : NatPrime p) : ZMod p :=
  zmodFromNat p prime.left (NatPrime_empty_absurd prime)
    (natFactorialFn (primePred p)) (natFactorialFn_unary (primePred_unary prime))

def zmodMinusOne {p : BHist} (prime : NatPrime p) : ZMod p :=
  zmodNeg p prime.left (NatPrime_empty_absurd prime)
    (zmodOne p prime.left (NatPrime_empty_absurd prime))

structure NonzeroResidue (p : BHist) where
  val : ZMod p
  nonzero : zmodNonzero val

def inversePairFactors {p : BHist} (prime : NatPrime p) :
    List (NonzeroResidue p) -> List (ZMod p)
  | [] => []
  | seed :: seeds =>
      seed.val :: zmodInv prime seed.val seed.nonzero ::
        inversePairFactors prime seeds

theorem inversePairFactors_product_one {p : BHist} (prime : NatPrime p) :
    ∀ seeds : List (NonzeroResidue p),
      zmodEq
        (listProd
          (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
          (inversePairFactors prime seeds))
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
  | [] => by
      exact zmodEq_refl (zmodOne p prime.left (NatPrime_empty_absurd prime))
  | seed :: seeds => by
      have tailProduct :
          zmodEq
            (listProd
              (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
              (inversePairFactors prime seeds))
            (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
        inversePairFactors_product_one prime seeds
      have pairProduct :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              seed.val (zmodInv prime seed.val seed.nonzero))
            (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
        zmodInv_mul prime seed.val seed.nonzero
      change
        zmodEq
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            seed.val
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodInv prime seed.val seed.nonzero)
              (listProd
                (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
                (inversePairFactors prime seeds))))
          (zmodOne p prime.left (NatPrime_empty_absurd prime))
      have reassociate :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodMul p prime.left (NatPrime_empty_absurd prime)
                seed.val (zmodInv prime seed.val seed.nonzero))
              (listProd
                (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
                (inversePairFactors prime seeds)))
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              seed.val
              (zmodMul p prime.left (NatPrime_empty_absurd prime)
                (zmodInv prime seed.val seed.nonzero)
                (listProd
                  (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
                  (inversePairFactors prime seeds)))) :=
        zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
          seed.val (zmodInv prime seed.val seed.nonzero)
          (listProd
            (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
            (inversePairFactors prime seeds))
      exact zmodEq_trans (zmodEq_symm reassociate)
        (zmodEq_trans
          (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
            pairProduct tailProduct)
          (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
            (zmodOne p prime.left (NatPrime_empty_absurd prime))))

theorem standardFixed_product_minus_one {p : BHist} (prime : NatPrime p) :
    zmodEq
      (listProd
        (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
        [zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime])
      (zmodMinusOne prime) := by
  change
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodMinusOne prime)
          (zmodOne p prime.left (NatPrime_empty_absurd prime))))
      (zmodMinusOne prime)
  exact zmodEq_trans
    (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (zmodEq_refl (zmodOne p prime.left (NatPrime_empty_absurd prime)))
      (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime)
        (zmodMinusOne prime)))
    (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
      (zmodMinusOne prime))

structure WilsonPairingData (p : BHist) (prime : NatPrime p) where
  residues : List (ZMod p)
  fixedFactors : List (ZMod p)
  pairSeeds : List (NonzeroResidue p)
  fixed_product :
    zmodEq
      (listProd
        (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
        fixedFactors)
      (zmodMinusOne prime)
  paired_residue_permutation :
    ListPerm residues (fixedFactors ++ inversePairFactors prime pairSeeds)
  factorial_product :
    zmodEq (wilsonFactorialResidue prime)
      (listProd
        (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
        residues)

theorem paired_tail_product_one {p : BHist} (prime : NatPrime p)
    (data : WilsonPairingData p prime) :
    zmodEq
      (listProd
        (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
        (inversePairFactors prime data.pairSeeds))
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
  inversePairFactors_product_one prime data.pairSeeds

theorem wilson_from_pairing_data {p : BHist} (prime : NatPrime p)
    (data : WilsonPairingData p prime) :
    zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) := by
  let R := zmodRelCommRing p prime.left (NatPrime_empty_absurd prime)
  have permProduct :
      zmodEq
        (listProd R data.residues)
        (listProd R (data.fixedFactors ++ inversePairFactors prime data.pairSeeds)) :=
    prod_permInvariant R data.paired_residue_permutation
  have appendProduct :
      zmodEq
        (listProd R (data.fixedFactors ++ inversePairFactors prime data.pairSeeds))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (listProd R data.fixedFactors)
          (listProd R (inversePairFactors prime data.pairSeeds))) :=
    prod_append R data.fixedFactors (inversePairFactors prime data.pairSeeds)
  have collapseTail :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (listProd R data.fixedFactors)
          (listProd R (inversePairFactors prime data.pairSeeds)))
        (zmodMinusOne prime) := by
    exact zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        data.fixed_product (paired_tail_product_one prime data))
      (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime)
        (zmodMinusOne prime))
  exact zmodEq_trans data.factorial_product
    (zmodEq_trans permProduct (zmodEq_trans appendProduct collapseTail))

theorem standard_pairing_product_minus_one {p : BHist} (prime : NatPrime p)
    (residues : List (ZMod p)) (pairSeeds : List (NonzeroResidue p)) :
    ListPerm residues
      ([zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime] ++
        inversePairFactors prime pairSeeds) ->
      zmodEq
        (listProd
          (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
          residues)
        (zmodMinusOne prime) := by
  intro perm
  let fixedFactors :=
    [zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime]
  let R := zmodRelCommRing p prime.left (NatPrime_empty_absurd prime)
  have permProduct :
      zmodEq
        (listProd R residues)
        (listProd R (fixedFactors ++ inversePairFactors prime pairSeeds)) :=
    prod_permInvariant R perm
  have appendProduct :
      zmodEq
        (listProd R (fixedFactors ++ inversePairFactors prime pairSeeds))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (listProd R fixedFactors)
          (listProd R (inversePairFactors prime pairSeeds))) :=
    prod_append R fixedFactors (inversePairFactors prime pairSeeds)
  have collapsed :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (listProd R fixedFactors)
          (listProd R (inversePairFactors prime pairSeeds)))
        (zmodMinusOne prime) := by
    exact zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (standardFixed_product_minus_one prime)
        (inversePairFactors_product_one prime pairSeeds))
      (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime)
        (zmodMinusOne prime))
  exact zmodEq_trans permProduct (zmodEq_trans appendProduct collapsed)

structure WilsonStandardPairingData (p : BHist) (prime : NatPrime p) where
  residues : List (ZMod p)
  pairSeeds : List (NonzeroResidue p)
  paired_residue_permutation :
    ListPerm residues
      ([zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime] ++
        inversePairFactors prime pairSeeds)
  factorial_product :
    zmodEq (wilsonFactorialResidue prime)
      (listProd
        (zmodRelCommRing p prime.left (NatPrime_empty_absurd prime))
        residues)

def WilsonStandardPairingData.toPairingData {p : BHist}
    {prime : NatPrime p} (data : WilsonStandardPairingData p prime) :
    WilsonPairingData p prime :=
  { residues := data.residues
    fixedFactors :=
      [zmodOne p prime.left (NatPrime_empty_absurd prime), zmodMinusOne prime]
    pairSeeds := data.pairSeeds
    fixed_product := standardFixed_product_minus_one prime
    paired_residue_permutation := data.paired_residue_permutation
    factorial_product := data.factorial_product }

theorem wilson_from_standard_pairing {p : BHist} (prime : NatPrime p)
    (data : WilsonStandardPairingData p prime) :
    zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) := by
  exact zmodEq_trans data.factorial_product
    (standard_pairing_product_minus_one prime data.residues data.pairSeeds
      data.paired_residue_permutation)

end BEDC.Derived.WilsonUp
