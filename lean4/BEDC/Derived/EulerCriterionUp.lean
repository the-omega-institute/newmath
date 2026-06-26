import BEDC.Derived.FermatLittleUp
import BEDC.Derived.WilsonTheoremUp

namespace BEDC.Derived.EulerCriterionUp

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Hist
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.FermatLittleUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.WilsonTheoremUp
open BEDC.Derived.WilsonUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

def eulerHalfExponent (p : BHist) (h : Nat) : Prop :=
  h + h = bwordLength p - 1

def eulerPower {p : BHist} (prime : NatPrime p) (a : ZMod p) (h : Nat) : ZMod p :=
  zmodPowNat prime a h

def eulerCriterionValue {p : BHist} (prime : NatPrime p) (a : ZMod p)
    (h : Nat) (s : BEDC.Algebra.Rel.IntegerUp) : Prop :=
  (LegendreClassifies prime a s ∧
      BEDC.Algebra.Rel.IntEq s legendreZero ∧
      zmodEq (eulerPower prime a h)
        (zmodZero p prime.left (NatPrime_empty_absurd prime))) ∨
    (LegendreClassifies prime a s ∧
      BEDC.Algebra.Rel.IntEq s legendreOne ∧
      zmodEq (eulerPower prime a h)
        (zmodOne p prime.left (NatPrime_empty_absurd prime))) ∨
      (LegendreClassifies prime a s ∧
        BEDC.Algebra.Rel.IntEq s legendreNegOne ∧
        zmodEq (eulerPower prime a h) (zmodMinusOne prime))

theorem fermatLittle_zmod_nonzero {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    zmodNonzero a ->
      zmodEq (zmodPowNat prime a (bwordLength p - 1))
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro aNonzero
  have atResidueLength :
      zmodEq (zmodPowNat prime a (nonzeroResidues prime).length)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    fermat_unit_list_permutation prime a aNonzero (nonzeroResidues prime)
      (nonzeroResidues_all_nonzero prime)
      (mulByUnit_permutes prime a aNonzero)
  rw [nonzeroResidues_length prime] at atResidueLength
  exact atResidueLength

private theorem zmodPowNat_succ_right {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (k : Nat) :
    zmodEq
      (zmodPowNat prime a (k + 1))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        a (zmodPowNat prime a k)) := by
  exact zmodEq_trans (zmodPowNat_succ prime a k)
    (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
      (zmodPowNat prime a k) a)

private theorem zmodPowNat_congr {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    zmodEq a b -> ∀ k : Nat,
      zmodEq (zmodPowNat prime a k) (zmodPowNat prime b k)
  | _same, 0 =>
      zmodEq_refl _
  | same, k + 1 =>
      zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodPowNat_congr prime same k) same

private theorem zmodPowNat_square_double {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    ∀ h : Nat,
      zmodEq
        (zmodPowNat prime (zmodSquare prime x) h)
        (zmodPowNat prime x (h + h))
  | 0 => by
      exact zmodEq_refl _
  | h + 1 => by
      let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
      have tail :
          zmodEq (zmodPowNat prime (zmodSquare prime x) h)
            (zmodPowNat prime x (h + h)) :=
        zmodPowNat_square_double prime x h
      have step :
          zmodEq (zmodPowNat prime (zmodSquare prime x) (h + 1))
            (mul (zmodPowNat prime (zmodSquare prime x) h)
              (zmodSquare prime x)) :=
        zmodPowNat_succ prime (zmodSquare prime x) h
      have replaceTail :
          zmodEq
            (mul (zmodPowNat prime (zmodSquare prime x) h)
              (zmodSquare prime x))
            (mul (zmodPowNat prime x (h + h)) (zmodSquare prime x)) :=
        zmodMul_congr prime.left (NatPrime_empty_absurd prime) tail
          (zmodEq_refl (zmodSquare prime x))
      have addShape : h + 1 + (h + 1) = (h + h) + 2 := by
        have moveOne : 1 + (h + 1) = h + (1 + 1) := by
          exact Eq.trans (Nat.add_assoc 1 h 1).symm
            (Eq.trans (congrArg (fun t : Nat => t + 1) (Nat.add_comm 1 h))
              (Nat.add_assoc h 1 1))
        exact Eq.trans (Nat.add_assoc h 1 (h + 1))
          (Eq.trans (congrArg (fun t : Nat => h + t) moveOne)
            (Eq.trans (Nat.add_assoc h h (1 + 1)).symm rfl))
      rw [addShape]
      change zmodEq (zmodPowNat prime (zmodSquare prime x) (h + 1))
        (zmodPowNat prime x ((h + h) + 2))
      exact zmodEq_trans step
        (zmodEq_trans replaceTail
          (zmodEq_symm (by
            change zmodEq
              (zmodPowNat prime x ((h + h) + 2))
              (mul (zmodPowNat prime x (h + h)) (zmodSquare prime x))
            rw [Nat.add_assoc]
            change zmodEq
              (zmodPowNat prime x ((h + h + 1) + 1))
              (mul (zmodPowNat prime x (h + h)) (zmodSquare prime x))
            exact zmodEq_trans
              (zmodPowNat_succ prime x (h + h + 1))
              (zmodEq_trans
                (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                  (zmodPowNat_succ prime x (h + h)) (zmodEq_refl x))
                (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
                  (zmodPowNat prime x (h + h)) x x)))))

private theorem square_root_nonzero {p : BHist} (prime : NatPrime p)
    {a x : ZMod p} :
    zmodEq (zmodSquare prime x) a -> zmodNonzero a -> zmodNonzero x := by
  intro squareEq aNonzero xZero
  have squareZero :
      zmodEq (zmodSquare prime x)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
    exact zmodEq_trans
      (zmodSquare_respects prime
        (show zmodEq x (zmodZero p prime.left (NatPrime_empty_absurd prime)) from
          xZero))
      (zmodMul_zero_left prime
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
  exact aNonzero (zmodEq_trans (zmodEq_symm squareEq) squareZero)

theorem quadraticResidue_eulerPower_one {p : BHist} (prime : NatPrime p)
    {a : ZMod p} {h : Nat} :
    eulerHalfExponent p h -> IsQR prime a -> zmodNonzero a ->
      zmodEq (eulerPower prime a h)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro half qr aNonzero
  cases qr with
  | intro x squareEq =>
      have xNonzero : zmodNonzero x :=
        square_root_nonzero prime squareEq aNonzero
      have powAtoSquare :
          zmodEq (eulerPower prime a h)
            (zmodPowNat prime (zmodSquare prime x) h) :=
        zmodPowNat_congr prime (zmodEq_symm squareEq) h
      have squarePow :
          zmodEq (zmodPowNat prime (zmodSquare prime x) h)
            (zmodPowNat prime x (h + h)) :=
        zmodPowNat_square_double prime x h
      have fermat :
          zmodEq (zmodPowNat prime x (bwordLength p - 1))
            (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
        fermatLittle_zmod_nonzero prime x xNonzero
      rw [half] at squarePow
      exact zmodEq_trans powAtoSquare (zmodEq_trans squarePow fermat)

def involutionPartner {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (x : NonzeroResidue p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime) a
    (zmodInv prime x.val x.nonzero)

def involutionPairFactors {p : BHist} (prime : NatPrime p)
    (a : ZMod p) : List (NonzeroResidue p) -> List (ZMod p)
  | [] => []
  | x :: xs =>
      x.val :: involutionPartner prime a x ::
        involutionPairFactors prime a xs

theorem involutionPair_product {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (x : NonzeroResidue p) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        x.val (involutionPartner prime a x))
      a := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  exact zmodEq_trans
    (zmodEq_symm
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
        x.val a (zmodInv prime x.val x.nonzero)))
    (zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodMul_comm prime.left (NatPrime_empty_absurd prime) x.val a)
        (zmodEq_refl (zmodInv prime x.val x.nonzero)))
      (zmodEq_trans
        (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
          a x.val (zmodInv prime x.val x.nonzero))
        (zmodEq_trans
          (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
            (zmodEq_refl a) (zmodInv_mul prime x.val x.nonzero))
          (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) a))))

theorem involutionPairFactors_product_power {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    ∀ seeds : List (NonzeroResidue p),
      zmodEq
        (listProd (zmodRelCommRing prime)
          (involutionPairFactors prime a seeds))
        (zmodPowNat prime a seeds.length)
  | [] => by
      exact zmodEq_refl (zmodOne p prime.left (NatPrime_empty_absurd prime))
  | seed :: seeds => by
      let R := zmodRelCommRing prime
      have tail :
          zmodEq
            (listProd R (involutionPairFactors prime a seeds))
            (zmodPowNat prime a seeds.length) :=
        involutionPairFactors_product_power prime a seeds
      change
        zmodEq
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            seed.val
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (involutionPartner prime a seed)
              (listProd R (involutionPairFactors prime a seeds))))
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            (zmodPowNat prime a seeds.length) a)
      have pairAssoc :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              seed.val
              (zmodMul p prime.left (NatPrime_empty_absurd prime)
                (involutionPartner prime a seed)
                (listProd R (involutionPairFactors prime a seeds))))
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodMul p prime.left (NatPrime_empty_absurd prime)
                seed.val (involutionPartner prime a seed))
              (listProd R (involutionPairFactors prime a seeds))) :=
        zmodEq_symm
          (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
            seed.val (involutionPartner prime a seed)
            (listProd R (involutionPairFactors prime a seeds)))
      have collapsePair :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodMul p prime.left (NatPrime_empty_absurd prime)
                seed.val (involutionPartner prime a seed))
              (listProd R (involutionPairFactors prime a seeds)))
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              a (zmodPowNat prime a seeds.length)) :=
        zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (involutionPair_product prime a seed) tail
      exact zmodEq_trans pairAssoc
        (zmodEq_trans collapsePair
          (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
            a (zmodPowNat prime a seeds.length)))

theorem fixedPointFreeInvolution_prod {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (seeds : List (NonzeroResidue p)) {h : Nat} :
    seeds.length = h ->
      ListPerm (nonzeroResidues prime) (involutionPairFactors prime a seeds) ->
        zmodEq
          (listProd (zmodRelCommRing prime) (nonzeroResidues prime))
          (zmodPowNat prime a h) := by
  intro lengthEq paired
  let R := zmodRelCommRing prime
  have permProduct :
      zmodEq
        (listProd R (nonzeroResidues prime))
        (listProd R (involutionPairFactors prime a seeds)) :=
    prod_permInvariant R paired
  have pairProduct :
      zmodEq
        (listProd R (involutionPairFactors prime a seeds))
        (zmodPowNat prime a seeds.length) :=
    involutionPairFactors_product_power prime a seeds
  rw [lengthEq] at pairProduct
  exact zmodEq_trans permProduct pairProduct

theorem eulerPower_minus_one_from_pairing {p : BHist}
    (prime : NatPrime p) {a : ZMod p} {h : Nat}
    (seeds : List (NonzeroResidue p)) :
    seeds.length = h ->
      ListPerm (nonzeroResidues prime) (involutionPairFactors prime a seeds) ->
        zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) ->
          zmodEq (eulerPower prime a h) (zmodMinusOne prime) := by
  intro lengthEq paired wilson
  have residueProduct :
      zmodEq
        (listProd (zmodRelCommRing prime) (nonzeroResidues prime))
        (zmodFactorialBelow prime) :=
    zmod_nonzeroResidues_prod_eq_factorial_mod prime
  have factorialSame :
      zmodEq (zmodFactorialBelow prime) (zmodMinusOne prime) := by
    exact zmodEq_trans
      (zmodEq_symm
        (show zmodEq (wilsonFactorialResidue prime) (zmodFactorialBelow prime) from
          by
            rfl))
      wilson
  have pairProduct :
      zmodEq
        (listProd (zmodRelCommRing prime) (nonzeroResidues prime))
        (eulerPower prime a h) :=
    fixedPointFreeInvolution_prod prime a seeds lengthEq paired
  exact zmodEq_trans (zmodEq_symm pairProduct)
    (zmodEq_trans residueProduct factorialSame)

theorem legendre_nonresidue_branch_from_pairing {p : BHist}
    (prime : NatPrime p) {a : ZMod p} {h : Nat}
    (seeds : List (NonzeroResidue p)) :
    seeds.length = h ->
      ListPerm (nonzeroResidues prime) (involutionPairFactors prime a seeds) ->
        zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime) ->
          LegendreNonresidue prime a ->
            eulerCriterionValue prime a h legendreNegOne := by
  intro lengthEq paired wilson nonresidue
  exact Or.inr (Or.inr
    ⟨legendreSym_nonresidue prime nonresidue,
      BEDC.Derived.RationalUp.IntEq_refl _,
      eulerPower_minus_one_from_pairing prime seeds lengthEq paired wilson⟩)

theorem legendre_residue_branch {p : BHist} (prime : NatPrime p)
    {a : ZMod p} {h : Nat} :
    eulerHalfExponent p h -> IsQR prime a -> zmodNonzero a ->
      eulerCriterionValue prime a h legendreOne := by
  intro half qr aNonzero
  exact Or.inr (Or.inl
    ⟨Or.inr (Or.inl
      ⟨qr, aNonzero, BEDC.Derived.RationalUp.IntEq_refl _⟩),
      BEDC.Derived.RationalUp.IntEq_refl _,
      quadraticResidue_eulerPower_one prime half qr aNonzero⟩)

end BEDC.Derived.EulerCriterionUp
