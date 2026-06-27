import BEDC.Derived.EulerCriterionUp
import BEDC.Derived.PolyRootBoundUp

namespace BEDC.Derived.LegendreDichotomyUp

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.Derived.EulerCriterionUp
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PolyRootBoundUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.WilsonUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

def zmodEqBool {p : BHist} (x y : ZMod p) : Bool :=
  if x.val = y.val then true else false

theorem zmodEqBool_true {p : BHist} {x y : ZMod p} :
    zmodEqBool x y = true -> zmodEq x y := by
  unfold zmodEqBool
  by_cases same : x.val = y.val
  · rw [if_pos same]
    intro _ok
    exact same
  · rw [if_neg same]
    intro impossible
    cases impossible

theorem zmodEqBool_of_zmodEq {p : BHist} {x y : ZMod p} :
    zmodEq x y -> zmodEqBool x y = true := by
  intro same
  unfold zmodEqBool
  have raw : x.val = y.val := same
  rw [if_pos raw]

def hasSquareRootInList {p : BHist} (prime : NatPrime p) (a : ZMod p) :
    List (ZMod p) -> Bool
  | [] => false
  | x :: xs =>
      if zmodEqBool (zmodSquare prime x) a = true then
        true
      else
        hasSquareRootInList prime a xs

theorem hasSquareRootInList_sound {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    ∀ xs : List (ZMod p),
      hasSquareRootInList prime a xs = true ->
        ∃ x : ZMod p, x ∈ xs ∧ zmodEq (zmodSquare prime x) a
  | [], found => by
      cases found
  | x :: xs, found => by
      unfold hasSquareRootInList at found
      by_cases hit : zmodEqBool (zmodSquare prime x) a = true
      · rw [if_pos hit] at found
        exact ⟨x, List.Mem.head xs, zmodEqBool_true hit⟩
      · rw [if_neg hit] at found
        cases hasSquareRootInList_sound prime a xs found with
        | intro y data =>
            exact ⟨y, List.Mem.tail x data.left, data.right⟩

theorem hasSquareRootInList_true_of_mem {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    ∀ {xs : List (ZMod p)} {x : ZMod p},
      x ∈ xs -> zmodEq (zmodSquare prime x) a ->
        hasSquareRootInList prime a xs = true
  | [], _x, mem, _root => by
      cases mem
  | y :: ys, x, mem, root => by
      unfold hasSquareRootInList
      cases mem with
      | head =>
          rw [zmodEqBool_of_zmodEq root]
          rfl
      | tail _ tailMem =>
          by_cases hit : zmodEqBool (zmodSquare prime y) a = true
          · rw [if_pos hit]
          · rw [if_neg hit]
            exact hasSquareRootInList_true_of_mem prime a tailMem root

def legendreQRSearch {p : BHist} (prime : NatPrime p) (a : ZMod p) : Bool :=
  hasSquareRootInList prime a (nonzeroResidues prime)

theorem legendreQRSearch_sound {p : BHist} (prime : NatPrime p)
    {a : ZMod p} :
    legendreQRSearch prime a = true -> IsQR prime a := by
  intro found
  cases hasSquareRootInList_sound prime a (nonzeroResidues prime) found with
  | intro x data =>
      exact ⟨x, data.right⟩

theorem square_root_nonzero {p : BHist} (prime : NatPrime p)
    {a x : ZMod p} :
    zmodEq (zmodSquare prime x) a -> zmodNonzero a -> zmodNonzero x := by
  intro squareEq aNonzero xZero
  have squareZero :
      zmodEq (zmodSquare prime x)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
    exact zmodEq_trans
      (zmodSquare_respects prime
        (show zmodEq x
          (zmodZero p prime.left (NatPrime_empty_absurd prime)) from xZero))
      (zmodMul_zero_left prime
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
  exact aNonzero (zmodEq_trans (zmodEq_symm squareEq) squareZero)

theorem legendreQRSearch_complete {p : BHist} (prime : NatPrime p)
    {a : ZMod p} :
    zmodNonzero a -> IsQR prime a -> legendreQRSearch prime a = true := by
  intro aNonzero qr
  cases qr with
  | intro x squareEq =>
      have xNonzero : zmodNonzero x :=
        square_root_nonzero prime squareEq aNonzero
      have xMem : x ∈ nonzeroResidues prime :=
        nonzero_residues_complete prime x xNonzero
      exact hasSquareRootInList_true_of_mem prime a xMem squareEq

theorem legendreQRSearch_false_of_nonresidue {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    LegendreNonresidue prime a -> legendreQRSearch prime a = false := by
  intro nonresidue
  cases found : legendreQRSearch prime a with
  | false =>
      rfl
  | true =>
      exact False.elim (nonresidue.right (legendreQRSearch_sound prime found))

theorem legendreQRSearch_nonresidue_of_false {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a -> legendreQRSearch prime a = false ->
      LegendreNonresidue prime a := by
  intro aNonzero notFound
  exact ⟨aNonzero,
    fun qr =>
      have found : legendreQRSearch prime a = true :=
        legendreQRSearch_complete prime aNonzero qr
      by
        rw [notFound] at found
        cases found⟩

theorem legendre_qr_nonresidue_dichotomy {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      (IsQR prime a ∧ (LegendreNonresidue prime a -> False)) ∨
        (LegendreNonresidue prime a ∧ (IsQR prime a -> False)) := by
  intro aNonzero
  cases found : legendreQRSearch prime a with
  | false =>
      have nonresidue : LegendreNonresidue prime a :=
        legendreQRSearch_nonresidue_of_false prime aNonzero found
      exact Or.inr ⟨nonresidue, nonresidue.right⟩
  | true =>
      have qr : IsQR prime a :=
        legendreQRSearch_sound prime found
      exact Or.inl
        ⟨qr, fun nonresidue => nonresidue.right qr⟩

theorem legendre_symbol_nonzero_pm_one {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      ∃ s : BEDC.Algebra.Rel.IntegerUp,
        LegendreClassifies prime a s ∧
          (BEDC.Algebra.Rel.IntEq s legendreOne ∨
            BEDC.Algebra.Rel.IntEq s legendreNegOne) := by
  intro aNonzero
  cases legendre_qr_nonresidue_dichotomy prime aNonzero with
  | inl qrBranch =>
      exact ⟨legendreOne,
        Or.inr (Or.inl
          ⟨qrBranch.left, aNonzero,
            BEDC.Derived.RationalUp.IntEq_refl _⟩),
        Or.inl (BEDC.Derived.RationalUp.IntEq_refl _)⟩
  | inr nonresidueBranch =>
      exact ⟨legendreNegOne,
        legendreSym_nonresidue prime nonresidueBranch.left,
        Or.inr (BEDC.Derived.RationalUp.IntEq_refl _)⟩

def squareRootPolynomial {p : BHist} (prime : NatPrime p) (a : ZMod p) :
    List (ZMod p) :=
  let R := zmodRing prime
  [R.neg a, R.zero, R.one]

theorem squareRootPolynomial_degree_exact_two {p : BHist}
    (prime : NatPrime p) (a : ZMod p) :
    PolyDegreeExact prime (squareRootPolynomial prime a) 2 := by
  unfold squareRootPolynomial
  exact polyDegreeExact_step prime
    (polyDegreeExact_step prime
      (polyDegreeExact_constant prime (zmodOne_nonzero prime)))

theorem polyEval_zero_one {p : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq
      (polyEval prime [(zmodRing prime).zero, (zmodRing prime).one] x)
      x := by
  let R := zmodRing prime
  change zmodEq (R.add R.zero (R.mul x (polyEval prime [R.one] x))) x
  exact R.trans
    (R.add_congr (R.refl R.zero)
      (R.mul_congr (R.refl x) (polyEval_singleton prime R.one x)))
    (R.trans (R.zero_add (R.mul x R.one)) (R.mul_one x))

theorem squareRootPolynomial_root_of_square {p : BHist}
    (prime : NatPrime p) {a x : ZMod p} :
    zmodEq (zmodSquare prime x) a ->
      PolyRoot prime (squareRootPolynomial prime a) x := by
  intro squareEq
  let R := zmodRing prime
  unfold squareRootPolynomial
  change zmodEq
    (R.add (R.neg a)
      (R.mul x
        (polyEval prime [R.zero, R.one] x))) R.zero
  have evalTail :
      zmodEq
        (R.mul x (polyEval prime [R.zero, R.one] x))
        (R.mul x x) :=
    R.mul_congr (R.refl x) (polyEval_zero_one prime x)
  exact R.trans
    (R.add_congr (R.refl (R.neg a)) evalTail)
    (R.trans
      (R.add_congr (R.refl (R.neg a)) squareEq)
      (R.neg_add a))

theorem squareRoot_list_bound {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (roots : List (ZMod p)) :
    ListNoDup roots ->
      (∀ x : ZMod p, x ∈ roots -> zmodEq (zmodSquare prime x) a) ->
        roots.length <= 2 := by
  intro nodup allRoots
  exact polyRootBound_list prime
    (squareRootPolynomial_degree_exact_two prime a)
    nodup
    (fun x mem => squareRootPolynomial_root_of_square prime (allRoots x mem))

theorem eulerCriterion_from_legendre_dichotomy_and_pairing {p : BHist}
    (prime : NatPrime p) {a : ZMod p} {h : Nat} :
    eulerHalfExponent p h ->
      zmodNonzero a ->
        (LegendreNonresidue prime a ->
          ∃ seeds : List (NonzeroResidue p),
            seeds.length = h ∧
              ListPerm (nonzeroResidues prime)
                (involutionPairFactors prime a seeds) ∧
              zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime)) ->
          ∃ s : BEDC.Algebra.Rel.IntegerUp,
            eulerCriterionValue prime a h s := by
  intro half aNonzero nonresiduePairing
  cases legendre_qr_nonresidue_dichotomy prime aNonzero with
  | inl qrBranch =>
      exact ⟨legendreOne,
        legendre_residue_branch prime half qrBranch.left aNonzero⟩
  | inr nonresidueBranch =>
      cases nonresiduePairing nonresidueBranch.left with
      | intro seeds data =>
          exact ⟨legendreNegOne,
            legendre_nonresidue_branch_from_pairing prime seeds
              data.left data.right.left data.right.right nonresidueBranch.left⟩

#check legendre_qr_nonresidue_dichotomy
#check legendre_symbol_nonzero_pm_one
#check squareRoot_list_bound
#check eulerCriterion_from_legendre_dichotomy_and_pairing

end BEDC.Derived.LegendreDichotomyUp
