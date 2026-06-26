import BEDC.Derived.FactorialResidueProduct

namespace BEDC.Derived.FermatLittleUp

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.ZModResidueList

abbrev NatOne : BHist := BHist.e1 BHist.Empty

private theorem positiveUpTo_length {n : BHist} :
    UnaryHistory n -> (positiveUpTo n).length = bwordLength n := by
  intro nUnary
  induction n with
  | Empty =>
      rfl
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      change Nat.succ (positiveUpTo tail).length =
        bwordLength (BHist.e1 tail)
      rw [ih (unary_e1_inversion nUnary)]
      rfl

theorem positiveBelow_length {p : BHist} :
    UnaryHistory p -> (positiveBelow p).length = bwordLength p - 1 := by
  intro pUnary
  cases p with
  | Empty =>
      rfl
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change (positiveUpTo tail).length = bwordLength (BHist.e1 tail) - 1
      rw [positiveUpTo_length (unary_e1_inversion pUnary)]
      rfl

theorem nonzeroResidues_length {p : BHist} (prime : NatPrime p) :
    (nonzeroResidues prime).length = bwordLength p - 1 := by
  unfold nonzeroResidues
  have rawLength :
      ∀ (xs : List BHist)
        (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p),
          (residueListFrom xs bounded).length = xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro _bounded
        rfl
    | cons r rs ih =>
        intro bounded
        change Nat.succ
          (residueListFrom rs
            (fun x mem => bounded x (List.Mem.tail r mem))).length =
          Nat.succ rs.length
        rw [ih (fun x mem => bounded x (List.Mem.tail r mem))]
  rw [rawLength (positiveBelow p)
    (fun _x mem => positiveBelow_member_lt prime.left mem)]
  exact positiveBelow_length prime.left

private theorem NatGcd_result_hsame_transport {a b g g' : BHist} :
    NatGcd a b g -> hsame g g' -> NatGcd a b g' := by
  intro gcd sameG
  constructor
  · exact NatGcd_left_unary gcd
  · constructor
    · exact NatGcd_right_unary gcd
    · constructor
      · exact unary_transport (NatGcd_result_unary gcd) sameG
      · constructor
        · exact (NatDivides_divisor_hsame_transport
            (NatGcd_dvd_left gcd) sameG).right
        · constructor
          · exact (NatDivides_divisor_hsame_transport
              (NatGcd_dvd_right gcd) sameG).right
          · intro d dividesA dividesB
            exact (NatDivides_dividend_hsame_transport
              (NatGcd_greatest gcd dividesA dividesB) sameG).right

private theorem NatPrime_gcd_one_of_not_divides {p a : BHist}
    (prime : NatPrime p) (aUnary : UnaryHistory a) :
    (NatDivides p a -> False) -> NatGcd a p NatOne := by
  intro notDivides
  let g := natGcdFn a p
  have gcdG : NatGcd a p g := natGcdFn_spec aUnary prime.left
  have gDividesP : NatDivides g p := NatGcd_dvd_right gcdG
  have gCases :
      hsame g NatOne ∨ hsame g p :=
    prime.right.right g (NatGcd_result_unary gcdG) gDividesP
  have gIsOne : hsame g NatOne := by
    cases gCases with
    | inl unit =>
        exact unit
    | inr sameP =>
        have pDividesA : NatDivides p a :=
          (NatDivides_divisor_hsame_transport
            (NatGcd_dvd_left gcdG) sameP).right
        exact False.elim (notDivides pDividesA)
  exact NatGcd_result_hsame_transport gcdG gIsOne

theorem fermatLittle_nonzero {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a) :
    NatGcd a p NatOne ->
      zmodEq
        (zmodPowNat prime
          (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
          (bwordLength p - 1))
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro gcd
  let aMod : ZMod p :=
    zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary
  let aNonzero : zmodNonzero aMod :=
    zmodFromNat_gcd_one_nonzero prime aUnary gcd
  have perm :
      ListPerm
        (List.map (zmodUnitMul prime aMod aNonzero)
          (nonzeroResidues prime))
        (nonzeroResidues prime) :=
    mulByCoprime_permutes prime aUnary gcd
  let R := zmodRelCommRing prime
  let residues := nonzeroResidues prime
  let factorialResidue := zmodFactorialBelow prime
  have permProduct :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime aMod aNonzero) residues))
        (listProd R residues) :=
    prod_permInvariant R perm
  have expandedProduct :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime aMod aNonzero) residues))
        (R.mul (zmodPowNat prime aMod residues.length)
          (listProd R residues)) :=
    zmodUnitMul_listProd_expansion prime aMod aNonzero residues
  have residueProductFactorial :
      zmodEq (listProd R residues) factorialResidue :=
    zmod_nonzeroResidues_prod_eq_factorial_mod prime
  have factorialNonzero : zmodNonzero factorialResidue :=
    zmodNonzero_respects residueProductFactorial
      (nonzeroResidues_nonempty_product_unit prime)
  have powTimesFactorial :
      zmodEq
        (R.mul (zmodPowNat prime aMod residues.length) factorialResidue)
        (R.mul R.one factorialResidue) := by
    exact zmodEq_trans
      (R.mul_congr
        (R.refl (zmodPowNat prime aMod residues.length))
        (zmodEq_symm residueProductFactorial))
      (zmodEq_trans
        (zmodEq_symm expandedProduct)
        (zmodEq_trans
          permProduct
          (zmodEq_trans
            residueProductFactorial
            (zmodEq_symm
              (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
                factorialResidue)))))
  have powAtList :
      zmodEq
        (zmodPowNat prime aMod (nonzeroResidues prime).length)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    zmodMul_right_cancel_nonzero prime factorialNonzero powTimesFactorial
  rw [nonzeroResidues_length prime] at powAtList
  exact powAtList

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

private theorem zmodPowNat_zero_base {p : BHist} (prime : NatPrime p)
    (k : Nat) :
    zmodEq
      (zmodPowNat prime
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) (k + 1))
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
  induction k with
  | zero =>
      change zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodOne p prime.left (NatPrime_empty_absurd prime))
          (zmodZero p prime.left (NatPrime_empty_absurd prime)))
        (zmodZero p prime.left (NatPrime_empty_absurd prime))
      exact BEDC.Derived.LegendreUp.zmodMul_zero_right prime
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
  | succ k ih =>
      exact zmodEq_trans
        (zmodPowNat_succ prime
          (zmodZero p prime.left (NatPrime_empty_absurd prime)) (k + 1))
        (zmodEq_trans
          (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
            ih (zmodEq_refl
              (zmodZero p prime.left (NatPrime_empty_absurd prime))))
          (BEDC.Derived.LegendreUp.zmodMul_zero_left prime
            (zmodZero p prime.left (NatPrime_empty_absurd prime))))

theorem fermatLittle_all {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a) :
    zmodEq
      (zmodPowNat prime
        (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
        (bwordLength p))
      (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary) := by
  let aMod : ZMod p :=
    zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary
  by_cases aZero : aMod.val = BHist.Empty
  · have aEqZero :
        zmodEq aMod (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
      exact aZero
    cases hLen : bwordLength p with
    | zero =>
        have pEmpty : hsame p BHist.Empty := by
          exact (NatUp_unary_standard_bridge.right.right.right.left
            prime.left unary_empty).mpr (by
              rw [hLen, NatUp_unary_standard_bridge.left])
        exact False.elim (NatPrime_empty_absurd prime pEmpty)
    | succ k =>
        have zeroPow :
            zmodEq
              (zmodPowNat prime
                (zmodZero p prime.left (NatPrime_empty_absurd prime))
                (k + 1))
              (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
          zmodPowNat_zero_base prime k
        have lift :
            zmodEq
              (zmodPowNat prime aMod (k + 1))
              (zmodPowNat prime
                (zmodZero p prime.left (NatPrime_empty_absurd prime))
                (k + 1)) :=
          zmodPowNat_congr prime aEqZero (k + 1)
        exact zmodEq_trans lift (zmodEq_trans zeroPow (zmodEq_symm aEqZero))
  · have aNonzero : zmodNonzero aMod := by
      intro empty
      exact aZero empty
    have gcd : NatGcd a p NatOne := by
      have pNotDividesA : NatDivides p a -> False := by
        intro divides
        have residueEmpty :
            hsame
              (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
                a aUnary).val
              BHist.Empty :=
          (dvd_iff_mod_zero prime.left (NatPrime_empty_absurd prime) aUnary).mp
            divides
        exact aNonzero residueEmpty
      exact NatPrime_gcd_one_of_not_divides prime aUnary pNotDividesA
    have powPred :
        zmodEq
          (zmodPowNat prime aMod (bwordLength p - 1))
          (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
      fermatLittle_nonzero prime aUnary gcd
    cases hLen : bwordLength p with
    | zero =>
        have pEmpty : hsame p BHist.Empty := by
          exact (NatUp_unary_standard_bridge.right.right.right.left
            prime.left unary_empty).mpr (by
              rw [hLen, NatUp_unary_standard_bridge.left])
        exact False.elim (NatPrime_empty_absurd prime pEmpty)
    | succ k =>
        change zmodEq (zmodPowNat prime aMod (k + 1)) aMod
        have predAtK :
            zmodEq (zmodPowNat prime aMod k)
              (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
          rw [hLen] at powPred
          exact powPred
        exact zmodEq_trans
          (zmodPowNat_succ_right prime aMod k)
          (zmodEq_trans
            (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
              (zmodEq_refl aMod) predAtK)
            (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) aMod))

end BEDC.Derived.FermatLittleUp
