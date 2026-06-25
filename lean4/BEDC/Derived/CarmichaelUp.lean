import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.FermatWilsonUp
import BEDC.Derived.PadicUp.IntegerTower.RingCompletion
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.ZModUp

set_option maxRecDepth 3000

namespace BEDC.Derived.CarmichaelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.ZModUp
open BEDC.Derived.EulerTheoremUp

abbrev NatTwo : BHist := natToUnary 2
abbrev NatThree : BHist := natToUnary 3
abbrev NatEleven : BHist := natToUnary 11
abbrev NatSeventeen : BHist := natToUnary 17
abbrev NatFiveHundredSixtyOne : BHist := natToUnary 561

private abbrev One : BHist := BEDC.Derived.PadicUp.NatOne

def NatComposite (n : BHist) : Prop :=
  UnaryHistory n ∧ NatUnaryStrictPrefix One n ∧
    ∃ d e : BHist, UnaryHistory d ∧ UnaryHistory e ∧
      NatUnaryStrictPrefix One d ∧ NatUnaryStrictPrefix One e ∧ NatMul d e n

def CarmichaelResidueCondition
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Prop :=
  ∀ a : ZMod n,
    NatGcd a.val n One ->
      zmodEq
        (zmodPowByNat n nUnary nNonempty a (bwordLength n - 1))
        (zmodOne n nUnary nNonempty)

def CarmichaelNumber (n : BHist) : Prop :=
  ∃ nUnary : UnaryHistory n, ∃ nNonempty : hsame n BHist.Empty -> False,
    NatComposite n ∧ CarmichaelResidueCondition n nUnary nNonempty

def PrimeFactorDividesPredecessor (p n : BHist) : Prop :=
  NatDivides (natSubUnary p One) (natSubUnary n One)

def KorseltFactorList (n : BHist) (factors : List BHist) : Prop :=
  PrimeFactorization n factors ∧ listSquarefree factors ∧
    ∀ p : BHist, p ∈ factors -> PrimeFactorDividesPredecessor p n

def CarmichaelViaKorselt (n : BHist) (factors : List BHist) : Prop :=
  NatComposite n ∧ KorseltFactorList n factors

theorem carmichaelViaKorselt_iff_components {n : BHist} {factors : List BHist} :
    CarmichaelViaKorselt n factors ↔
      NatComposite n ∧ PrimeFactorization n factors ∧ listSquarefree factors ∧
        ∀ p : BHist, p ∈ factors -> PrimeFactorDividesPredecessor p n := by
  constructor
  · intro cert
    exact ⟨cert.left, cert.right.left, cert.right.right.left, cert.right.right.right⟩
  · intro data
    exact ⟨data.left, data.right.left, data.right.right.left, data.right.right.right⟩

theorem korselt_forward_components {n : BHist} {factors : List BHist} :
    CarmichaelViaKorselt n factors ->
      PrimeFactorization n factors ∧ listSquarefree factors ∧
        ∀ p : BHist, p ∈ factors -> PrimeFactorDividesPredecessor p n := by
  intro cert
  exact ⟨cert.right.left, cert.right.right.left, cert.right.right.right⟩

theorem korselt_prime_factor_direction {n : BHist} {factors : List BHist}
    {p : BHist} :
    CarmichaelViaKorselt n factors -> p ∈ factors ->
      PrimeFactorDividesPredecessor p n := by
  intro cert mem
  exact cert.right.right.right p mem

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix One (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append One tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem NatOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix One (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix One (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        (NatUp_unary_standard_bridge.right.right.right.left
          resultData.left (natToUnary_unary _)).mpr (by
            rw [NatMul_bwordLength resultData.right]
            rw [natToUnary_length, natToUnary_length, natToUnary_length])
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem NatThree_prime : NatPrime NatThree := by
  have large : NatUnaryStrictPrefix One NatThree := by
    exact NatOne_strict_natToUnary_succ_succ 1
  exact minFactor_prime large

theorem NatEleven_prime : NatPrime NatEleven := by
  have large : NatUnaryStrictPrefix One NatEleven := by
    exact NatOne_strict_natToUnary_succ_succ 9
  exact minFactor_prime large

theorem NatSeventeen_prime : NatPrime NatSeventeen := by
  have large : NatUnaryStrictPrefix One NatSeventeen := by
    exact NatOne_strict_natToUnary_succ_succ 15
  exact minFactor_prime large

theorem NatThree_mul_NatEleven :
    NatMul NatThree NatEleven (natToUnary 33) := by
  exact natToUnary_mul_rel 3 11

theorem NatThirtyThree_mul_NatSeventeen :
    NatMul (natToUnary 33) NatSeventeen NatFiveHundredSixtyOne := by
  exact natToUnary_mul_rel 33 17

theorem carmichael561_factorization :
    PrimeFactorization NatFiveHundredSixtyOne [NatThree, NatEleven, NatSeventeen] := by
  constructor
  · exact natToUnary_unary 561
  · exact ⟨NatThree_prime, natToUnary 187,
      ⟨NatEleven_prime, natToUnary 17,
        ⟨NatSeventeen_prime, One,
          hsame_refl One,
          (NatMul_unit_right_iff NatSeventeen_prime.left).mpr (hsame_refl NatSeventeen)⟩,
        (natToUnary_mul_rel 11 17)⟩,
      natToUnary_mul_rel 3 187⟩

private theorem NatThree_ne_NatEleven : NatThree = NatEleven -> False := by
  intro same
  unfold NatThree NatEleven at same
  cases same

private theorem NatThree_ne_NatSeventeen : NatThree = NatSeventeen -> False := by
  intro same
  unfold NatThree NatSeventeen at same
  cases same

private theorem NatEleven_ne_NatSeventeen : NatEleven = NatSeventeen -> False := by
  intro same
  unfold NatEleven NatSeventeen at same
  cases same

private theorem listContainsPrime_NatThree_tail :
    listContainsPrime NatThree [NatEleven, NatSeventeen] = false := by
  change (if NatThree = NatEleven then true else
    if NatThree = NatSeventeen then true else false) = false
  cases h11 : (inferInstance : Decidable (NatThree = NatEleven)) with
  | isTrue same =>
      exact False.elim (NatThree_ne_NatEleven same)
  | isFalse _notSame =>
      cases h17 : (inferInstance : Decidable (NatThree = NatSeventeen)) with
      | isTrue same =>
          exact False.elim (NatThree_ne_NatSeventeen same)
      | isFalse _notSame =>
          rfl

private theorem listContainsPrime_NatEleven_tail :
    listContainsPrime NatEleven [NatSeventeen] = false := by
  change (if NatEleven = NatSeventeen then true else false) = false
  cases h17 : (inferInstance : Decidable (NatEleven = NatSeventeen)) with
  | isTrue same =>
      exact False.elim (NatEleven_ne_NatSeventeen same)
  | isFalse _notSame =>
      rfl

theorem carmichael561_squarefree :
    listSquarefree [NatThree, NatEleven, NatSeventeen] := by
  unfold listSquarefree
  exact ⟨listContainsPrime_NatThree_tail, listContainsPrime_NatEleven_tail, rfl, trivial⟩

theorem three_minus_one_divides_560 :
    PrimeFactorDividesPredecessor NatThree NatFiveHundredSixtyOne := by
  unfold PrimeFactorDividesPredecessor NatThree NatFiveHundredSixtyOne One natSubUnary
  change NatDivides (natToUnary 2) (natToUnary 560)
  exact ⟨natToUnary 280, natToUnary_unary 280, natToUnary_mul_rel 2 280⟩

theorem eleven_minus_one_divides_560 :
    PrimeFactorDividesPredecessor NatEleven NatFiveHundredSixtyOne := by
  unfold PrimeFactorDividesPredecessor NatEleven NatFiveHundredSixtyOne One natSubUnary
  change NatDivides (natToUnary 10) (natToUnary 560)
  exact ⟨natToUnary 56, natToUnary_unary 56, natToUnary_mul_rel 10 56⟩

theorem seventeen_minus_one_divides_560 :
    PrimeFactorDividesPredecessor NatSeventeen NatFiveHundredSixtyOne := by
  unfold PrimeFactorDividesPredecessor NatSeventeen NatFiveHundredSixtyOne One natSubUnary
  change NatDivides (natToUnary 16) (natToUnary 560)
  exact ⟨natToUnary 35, natToUnary_unary 35, natToUnary_mul_rel 16 35⟩

theorem carmichael561_korselt_factors :
    KorseltFactorList NatFiveHundredSixtyOne [NatThree, NatEleven, NatSeventeen] := by
  constructor
  · exact carmichael561_factorization
  · constructor
    · exact carmichael561_squarefree
    · intro p mem
      cases mem with
      | head =>
          exact three_minus_one_divides_560
      | tail _ memTail =>
          cases memTail with
          | head =>
              exact eleven_minus_one_divides_560
          | tail _ memLast =>
              cases memLast with
              | head =>
                  exact seventeen_minus_one_divides_560
              | tail _ memNil =>
                  cases memNil

theorem carmichael561_composite :
    NatComposite NatFiveHundredSixtyOne := by
  constructor
  · exact natToUnary_unary 561
  · constructor
    · exact NatOne_strict_natToUnary_succ_succ 559
    · exact ⟨NatThree, natToUnary 187,
        natToUnary_unary 3, natToUnary_unary 187,
        NatOne_strict_natToUnary_succ_succ 1,
        NatOne_strict_natToUnary_succ_succ 185,
        natToUnary_mul_rel 3 187⟩

theorem carmichael561_korselt :
    CarmichaelViaKorselt NatFiveHundredSixtyOne
      [NatThree, NatEleven, NatSeventeen] := by
  exact ⟨carmichael561_composite, carmichael561_korselt_factors⟩

end BEDC.Derived.CarmichaelUp
