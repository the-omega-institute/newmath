import BEDC.Derived.CarmichaelNumberUp
import BEDC.Derived.DivisorFunctionUp

set_option maxRecDepth 3000

namespace BEDC.Derived.LucasCarmichaelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.ArithmeticFnUp

abbrev NatOne : BHist := BEDC.Derived.PadicUp.NatOne
abbrev NatThree : BHist := natToUnary 3
abbrev NatSeven : BHist := natToUnary 7
abbrev NatNineteen : BHist := natToUnary 19
abbrev NatOneHundredThirtyThree : BHist := natToUnary 133
abbrev NatThreeHundredNinetyNine : BHist := natToUnary 399

inductive PrimeFactorShift where
  | predecessor
  | successor

def shiftedPrimeFactor (shift : PrimeFactorShift) (p : BHist) : BHist :=
  match shift with
  | PrimeFactorShift.predecessor => natSubUnary p NatOne
  | PrimeFactorShift.successor => append p NatOne

def shiftedNumber (shift : PrimeFactorShift) (n : BHist) : BHist :=
  match shift with
  | PrimeFactorShift.predecessor => natSubUnary n NatOne
  | PrimeFactorShift.successor => append n NatOne

def ShiftedPrimeFactorDivides (shift : PrimeFactorShift) (p n : BHist) : Prop :=
  NatDivides (shiftedPrimeFactor shift p) (shiftedNumber shift n)

def PrimeFactorDividesSuccessor (p n : BHist) : Prop :=
  ShiftedPrimeFactorDivides PrimeFactorShift.successor p n

def LucasCarmichaelFactorList (n : BHist) (factors : List BHist) : Prop :=
  PrimeFactorization n factors ∧ listSquarefree factors ∧
    ∀ p : BHist, p ∈ factors -> PrimeFactorDividesSuccessor p n

def LucasCarmichaelViaKorselt (n : BHist) (factors : List BHist) : Prop :=
  BEDC.Derived.CarmichaelUp.NatComposite n ∧
    LucasCarmichaelFactorList n factors

def LucasCarmichaelNumber (n : BHist) : Prop :=
  ∃ factors : List BHist, LucasCarmichaelViaKorselt n factors

theorem shiftedPrimeFactorDivides_predecessor {p n : BHist} :
    ShiftedPrimeFactorDivides PrimeFactorShift.predecessor p n ↔
      BEDC.Derived.CarmichaelUp.PrimeFactorDividesPredecessor p n := by
  rfl

theorem shiftedPrimeFactorDivides_successor {p n : BHist} :
    ShiftedPrimeFactorDivides PrimeFactorShift.successor p n ↔
      PrimeFactorDividesSuccessor p n := by
  rfl

theorem lucasCarmichaelViaKorselt_iff_components {n : BHist} {factors : List BHist} :
    LucasCarmichaelViaKorselt n factors ↔
      BEDC.Derived.CarmichaelUp.NatComposite n ∧
        PrimeFactorization n factors ∧ listSquarefree factors ∧
          ∀ p : BHist, p ∈ factors -> PrimeFactorDividesSuccessor p n := by
  constructor
  · intro cert
    exact ⟨cert.left, cert.right.left, cert.right.right.left,
      cert.right.right.right⟩
  · intro data
    exact ⟨data.left, data.right.left, data.right.right.left,
      data.right.right.right⟩

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem NatOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
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
  have large : NatUnaryStrictPrefix NatOne NatThree := by
    exact NatOne_strict_natToUnary_succ_succ 1
  exact minFactor_prime large

theorem NatSeven_prime : NatPrime NatSeven := by
  have large : NatUnaryStrictPrefix NatOne NatSeven := by
    exact NatOne_strict_natToUnary_succ_succ 5
  exact minFactor_prime large

theorem NatNineteen_prime : NatPrime NatNineteen := by
  have large : NatUnaryStrictPrefix NatOne NatNineteen := by
    exact NatOne_strict_natToUnary_succ_succ 17
  exact minFactor_prime large

theorem NatSeven_mul_NatNineteen :
    NatMul NatSeven NatNineteen NatOneHundredThirtyThree := by
  exact natToUnary_mul_rel 7 19

theorem NatThree_mul_NatOneHundredThirtyThree :
    NatMul NatThree NatOneHundredThirtyThree NatThreeHundredNinetyNine := by
  exact natToUnary_mul_rel 3 133

theorem lucasCarmichael399_factorization :
    PrimeFactorization NatThreeHundredNinetyNine
      [NatThree, NatSeven, NatNineteen] := by
  constructor
  · exact natToUnary_unary 399
  · exact ⟨NatThree_prime, NatOneHundredThirtyThree,
      ⟨NatSeven_prime, NatNineteen,
        ⟨NatNineteen_prime, NatOne,
          hsame_refl NatOne,
          (NatMul_unit_right_iff NatNineteen_prime.left).mpr
            (hsame_refl NatNineteen)⟩,
        NatSeven_mul_NatNineteen⟩,
      NatThree_mul_NatOneHundredThirtyThree⟩

private theorem NatThree_ne_NatSeven : NatThree = NatSeven -> False := by
  intro same
  unfold NatThree NatSeven at same
  cases same

private theorem NatThree_ne_NatNineteen : NatThree = NatNineteen -> False := by
  intro same
  unfold NatThree NatNineteen at same
  cases same

private theorem NatSeven_ne_NatNineteen : NatSeven = NatNineteen -> False := by
  intro same
  unfold NatSeven NatNineteen at same
  cases same

private theorem listContainsPrime_NatThree_tail :
    listContainsPrime NatThree [NatSeven, NatNineteen] = false := by
  change (if NatThree = NatSeven then true else
    if NatThree = NatNineteen then true else false) = false
  cases h7 : (inferInstance : Decidable (NatThree = NatSeven)) with
  | isTrue same =>
      exact False.elim (NatThree_ne_NatSeven same)
  | isFalse _notSame =>
      cases h19 : (inferInstance : Decidable (NatThree = NatNineteen)) with
      | isTrue same =>
          exact False.elim (NatThree_ne_NatNineteen same)
      | isFalse _notSame =>
          rfl

private theorem listContainsPrime_NatSeven_tail :
    listContainsPrime NatSeven [NatNineteen] = false := by
  change (if NatSeven = NatNineteen then true else false) = false
  cases h19 : (inferInstance : Decidable (NatSeven = NatNineteen)) with
  | isTrue same =>
      exact False.elim (NatSeven_ne_NatNineteen same)
  | isFalse _notSame =>
      rfl

theorem lucasCarmichael399_squarefree :
    listSquarefree [NatThree, NatSeven, NatNineteen] := by
  unfold listSquarefree
  exact ⟨listContainsPrime_NatThree_tail, listContainsPrime_NatSeven_tail, rfl, trivial⟩

theorem three_plus_one_divides_400 :
    PrimeFactorDividesSuccessor NatThree NatThreeHundredNinetyNine := by
  unfold PrimeFactorDividesSuccessor ShiftedPrimeFactorDivides shiftedPrimeFactor
    shiftedNumber NatThree NatThreeHundredNinetyNine NatOne
  change NatDivides (natToUnary 4) (natToUnary 400)
  exact ⟨natToUnary 100, natToUnary_unary 100, natToUnary_mul_rel 4 100⟩

theorem seven_plus_one_divides_400 :
    PrimeFactorDividesSuccessor NatSeven NatThreeHundredNinetyNine := by
  unfold PrimeFactorDividesSuccessor ShiftedPrimeFactorDivides shiftedPrimeFactor
    shiftedNumber NatSeven NatThreeHundredNinetyNine NatOne
  change NatDivides (natToUnary 8) (natToUnary 400)
  exact ⟨natToUnary 50, natToUnary_unary 50, natToUnary_mul_rel 8 50⟩

theorem nineteen_plus_one_divides_400 :
    PrimeFactorDividesSuccessor NatNineteen NatThreeHundredNinetyNine := by
  unfold PrimeFactorDividesSuccessor ShiftedPrimeFactorDivides shiftedPrimeFactor
    shiftedNumber NatNineteen NatThreeHundredNinetyNine NatOne
  change NatDivides (natToUnary 20) (natToUnary 400)
  exact ⟨natToUnary 20, natToUnary_unary 20, natToUnary_mul_rel 20 20⟩

theorem lucasCarmichael399_factor_list :
    LucasCarmichaelFactorList NatThreeHundredNinetyNine
      [NatThree, NatSeven, NatNineteen] := by
  constructor
  · exact lucasCarmichael399_factorization
  · constructor
    · exact lucasCarmichael399_squarefree
    · intro p mem
      cases mem with
      | head =>
          exact three_plus_one_divides_400
      | tail _ memTail =>
          cases memTail with
          | head =>
              exact seven_plus_one_divides_400
          | tail _ memLast =>
              cases memLast with
              | head =>
                  exact nineteen_plus_one_divides_400
              | tail _ memNil =>
                  cases memNil

theorem lucasCarmichael399_composite :
    BEDC.Derived.CarmichaelUp.NatComposite NatThreeHundredNinetyNine := by
  constructor
  · exact natToUnary_unary 399
  · constructor
    · exact NatOne_strict_natToUnary_succ_succ 397
    · exact ⟨NatThree, NatOneHundredThirtyThree,
        natToUnary_unary 3, natToUnary_unary 133,
        NatOne_strict_natToUnary_succ_succ 1,
        NatOne_strict_natToUnary_succ_succ 131,
        NatThree_mul_NatOneHundredThirtyThree⟩

theorem lucasCarmichael399_korselt :
    LucasCarmichaelViaKorselt NatThreeHundredNinetyNine
      [NatThree, NatSeven, NatNineteen] := by
  exact ⟨lucasCarmichael399_composite, lucasCarmichael399_factor_list⟩

theorem lucasCarmichael399_number :
    LucasCarmichaelNumber NatThreeHundredNinetyNine := by
  exact ⟨[NatThree, NatSeven, NatNineteen], lucasCarmichael399_korselt⟩

theorem lucasCarmichael399_components :
    BEDC.Derived.CarmichaelUp.NatComposite NatThreeHundredNinetyNine ∧
      PrimeFactorization NatThreeHundredNinetyNine
        [NatThree, NatSeven, NatNineteen] ∧
      listSquarefree [NatThree, NatSeven, NatNineteen] ∧
        ∀ p : BHist, p ∈ [NatThree, NatSeven, NatNineteen] ->
          PrimeFactorDividesSuccessor p NatThreeHundredNinetyNine := by
  exact lucasCarmichaelViaKorselt_iff_components.mp lucasCarmichael399_korselt

end BEDC.Derived.LucasCarmichaelUp
