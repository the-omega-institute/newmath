import BEDC.Derived.BoxStreamSqrt2Up
import BEDC.Derived.RationalUp.MetricOrder
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.PadicUp.Multiplicative

namespace BEDC.Derived.Sqrt2IrrationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.BoxStreamSqrt2Up

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact
    (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
      hUnary kUnary).mpr lengthEq

private theorem IntEq_zero_of_magnitude_empty {x : IntegerUp} :
    hsame x.magnitude BHist.Empty -> IntEq x intZero := by
  intro magEmpty
  cases x with
  | mk sign magnitude carrier =>
      cases sign with
      | b0 =>
          unfold IntEq intZero intOfNat intToPair
          apply IntPairClassifier_of_length_eq
          · exact ⟨carrier.right, unary_empty⟩
          · exact ⟨unary_empty, unary_empty⟩
          change
            bwordLength magnitude + bwordLength BHist.Empty =
              bwordLength BHist.Empty + bwordLength BHist.Empty
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [Nat.add_zero, Nat.zero_add]
          exact congrArg bwordLength magEmpty
      | b1 =>
          unfold IntEq intZero intOfNat intToPair
          apply IntPairClassifier_of_length_eq
          · exact ⟨unary_empty, carrier.right⟩
          · exact ⟨unary_empty, unary_empty⟩
          change
            bwordLength BHist.Empty + bwordLength BHist.Empty =
              bwordLength BHist.Empty + bwordLength magnitude
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [Nat.zero_add, Nat.zero_add]
          exact (congrArg bwordLength magEmpty).symm

theorem RatEq_zero_of_num_intEq {x : RatNum} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem RatEq_zero_of_num_magnitude_empty {x : RatNum} :
    hsame x.num.magnitude BHist.Empty -> RatEq x ratZero := by
  intro magEmpty
  exact RatEq_zero_of_num_intEq (IntEq_zero_of_magnitude_empty magEmpty)

theorem ratTwo_not_RatEq_zero : RatEq ratTwo ratZero -> False := by
  intro same
  have numZero : IntEq ratTwo.num intZero := RatEq_zero_num same
  have lenEq := IntPairClassifier_length_eq numZero
  unfold ratTwo intTwo intToRat intZero intOfNat intToPair at lenEq
  change bwordLength natTwo + bwordLength BHist.Empty =
    bwordLength BHist.Empty + bwordLength BHist.Empty at lenEq
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenEq
  rw [Nat.add_zero, Nat.zero_add] at lenEq
  change 2 = 0 at lenEq
  cases lenEq

private theorem ratMul_zero_zero :
    RatEq (ratMul ratZero ratZero) ratZero := by
  apply RatEq_zero_of_num_intEq
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero intZero) intZero
  exact intMul_zero_left intZero

private theorem ratSquare_zero_of_RatEq_zero {q : RatNum} :
    RatEq q ratZero -> RatEq (ratMul q q) ratZero := by
  intro qZero
  exact RatEq_trans (ratMul q q) (ratMul ratZero ratZero) ratZero
    (ratMul_respects qZero qZero) ratMul_zero_zero

private theorem ratApart0_of_square_eq_two {q : RatNum} :
    RatEq (ratMul q q) ratTwo -> ratApart0 q := by
  intro squareEq
  unfold ratApart0 intApart0
  cases q with
  | mk num den den_pos =>
      cases num with
      | mk sign magnitude carrier =>
          cases magnitude with
          | Empty =>
              have qZero :
                  RatEq
                    { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                      den := den,
                      den_pos := den_pos } ratZero :=
                RatEq_zero_of_num_magnitude_empty (hsame_refl BHist.Empty)
              have squareZero :
                  RatEq
                    (ratMul
                      { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                        den := den,
                        den_pos := den_pos }
                      { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                        den := den,
                        den_pos := den_pos }) ratZero :=
                ratSquare_zero_of_RatEq_zero qZero
              have twoZero : RatEq ratTwo ratZero :=
                RatEq_trans ratTwo
                  (ratMul
                    { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                      den := den,
                      den_pos := den_pos }
                    { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                      den := den,
                      den_pos := den_pos }) ratZero
                  (RatEq_symm squareEq) squareZero
              exact False.elim (ratTwo_not_RatEq_zero twoZero)
          | e0 tail =>
              cases carrier.right
          | e1 tail =>
              have tailUnary : UnaryHistory tail := carrier.right
              cases tail with
              | Empty =>
                  exact Or.inr (hsame_refl NatOne)
              | e0 inner =>
                  cases tailUnary
              | e1 inner =>
                  exact Or.inl
                    ⟨BHist.e1 inner, tailUnary, (fun tailEmpty => by cases tailEmpty), by
                      have appended :
                          append NatOne (BHist.e1 inner) = BHist.e1 (BHist.e1 inner) :=
                        (BEDC.FKernel.Unary.unary_append_e1_left
                          (h := BHist.e1 inner) (k := BHist.Empty) tailUnary).trans
                          (congrArg BHist.e1 (append_empty_left (BHist.e1 inner)))
                      exact cont_intro appended.symm⟩

private def natEven : Nat -> Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (Nat.succ n) => natEven n

private theorem natEven_double : ∀ n : Nat, natEven (n + n) = true := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEven (Nat.succ (Nat.succ (n + n))) = true
      exact ih

private theorem natEven_succ_double : ∀ n : Nat,
    natEven (Nat.succ (n + n)) = false := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEven (Nat.succ (n + n)) = false
      exact ih

private theorem not_double_eq_succ_double {a b : Nat} :
    a + a = Nat.succ (b + b) -> False := by
  intro h
  have parity := congrArg natEven h
  rw [natEven_double a, natEven_succ_double b] at parity
  cases parity

private theorem ratValAdd_self_not_unit {j : BHist × BHist}
    (jCarrier : IntPairCarrier j.1 j.2) :
    IntPairClassifier (ratValAdd j j) (NatOne, BHist.Empty) -> False := by
  intro same
  have lenEq := IntPairClassifier_length_eq same
  unfold ratValAdd at lenEq
  rw [pairAdd_pos_length j j jCarrier jCarrier] at lenEq
  rw [pairAdd_neg_length j j jCarrier jCarrier] at lenEq
  change
    (bwordLength j.1 + bwordLength j.1) + bwordLength BHist.Empty =
      bwordLength NatOne + (bwordLength j.2 + bwordLength j.2) at lenEq
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenEq
  change
    (bwordLength j.1 + bwordLength j.1) + 0 =
      1 + (bwordLength j.2 + bwordLength j.2) at lenEq
  rw [Nat.add_zero, Nat.one_add] at lenEq
  change
    bwordLength j.1 + bwordLength j.1 =
      Nat.succ (bwordLength j.2 + bwordLength j.2) at lenEq
  exact not_double_eq_succ_double lenEq

private theorem natTwo_not_unit : hsame natTwo NatOne -> False := by
  intro same
  exact not_hsame_e1_empty (BEDC.FKernel.Hist.hsame_e1_iff.mp same)

theorem ratVal_natTwo_ratTwo :
    ratVal natTwo ratTwo (NatOne, BHist.Empty) := by
  unfold ratVal ratTwo intTwo intToRat intOfNat
  constructor
  · exact ⟨⟨Or.inl rfl, natTwo_unary⟩, NatPrime_self_valuation_one natTwo_prime⟩
  · constructor
    · exact ⟨⟨Or.inl rfl, unary_e1_closed unary_empty⟩,
        IsPadicValNat_zero_of_not_p_dvd natTwo_prime.left
          (unary_e1_closed unary_empty)
          (fun divides => natTwo_not_unit (NatDivides_unit_right_iff.mp divides))⟩
    · exact ⟨unary_e1_closed unary_empty, unary_empty⟩

theorem sqrt2_irrational :
    ∀ q : RatNum, ¬ RatEq (ratMul q q) ratTwo := by
  intro q squareEq
  have qApart : ratApart0 q := ratApart0_of_square_eq_two squareEq
  have product := rational_product_formula q qApart
  cases product with
  | intro numEntries productTail =>
      cases productTail with
      | intro denEntries data =>
          let j : BHist × BHist :=
            (primeCount natTwo numEntries, primeCount natTwo denEntries)
          have qVal : ratVal natTwo q j := by
            exact data.right.right.right.left natTwo_prime
          have squareVal :
              ratVal natTwo (ratMul q q) (ratValAdd j j) :=
            ratVal_mul natTwo_prime qVal qVal
          have sameIndex :
              IntPairClassifier (ratValAdd j j) (NatOne, BHist.Empty) :=
            ratVal_well_defined natTwo_prime squareEq squareVal ratVal_natTwo_ratTwo
          exact ratValAdd_self_not_unit qVal.right.right sameIndex

end BEDC.Derived.Sqrt2IrrationalUp
