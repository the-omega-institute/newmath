import BEDC.Derived.BernoulliUp
import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.PrimeUp.UniqueFactorization

set_option maxRecDepth 3000

namespace BEDC.Derived.VonStaudtClausenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.BernoulliUp
open BEDC.Derived.RationalUp

abbrev NatTwo : BHist := natToUnary 2
abbrev NatThree : BHist := natToUnary 3
abbrev NatFive : BHist := natToUnary 5
abbrev NatSeven : BHist := natToUnary 7
abbrev NatSix : BHist := natToUnary 6
abbrev NatThirty : BHist := natToUnary 30
abbrev NatFortyTwo : BHist := natToUnary 42

def rawUnitFraction (p : Nat) : RawRat :=
  rawNormalize { num := 1, denMinusOne := p - 1 }

def rawClausenSum (n : Nat) : List Nat -> RawRat
  | [] => rawBernoulli (2 * n)
  | p :: ps => rawAdd (rawUnitFraction p) (rawClausenSum n ps)

def clausePrimeCandidates (n : Nat) : List Nat :=
  (List.range (2 * n + 2)).filter
    (fun p => Nat.beq ((2 * n) % (p - 1)) 0 && Nat.beq (minFactorNat p) p)

def clauseDenominatorProductNat (n : Nat) : Nat :=
  (clausePrimeCandidates n).foldr (fun p acc => p * acc) 1

def rawBernoulliDenominator (n : Nat) : Nat :=
  (rawBernoulli n).den

def bernoulliDenominator (n : Nat) : BHist :=
  natToUnary (rawBernoulliDenominator n)

def clauseDenominatorProduct (n : Nat) : BHist :=
  natToUnary (clauseDenominatorProductNat n)

def rawRatIntegral (x : RawRat) : Prop :=
  x.den = 1

def rawVonStaudtClausenIntegralAt (n : Nat) : Prop :=
  rawRatIntegral (rawClausenSum n (clausePrimeCandidates n))

def rawBernoulliDenominatorMatchesClausenAt (n : Nat) : Prop :=
  rawBernoulliDenominator (2 * n) = clauseDenominatorProductNat n

def bernoulliDenominatorMatchesClausenAt (n : Nat) : Prop :=
  hsame (bernoulliDenominator (2 * n)) (clauseDenominatorProduct n)

theorem rawBernoulli_six_value :
    rawBernoulli 6 = { num := 1, denMinusOne := 41 } := by
  rfl

theorem rawUnitFraction_two_value :
    rawUnitFraction 2 = { num := 1, denMinusOne := 1 } := by
  rfl

theorem rawUnitFraction_three_value :
    rawUnitFraction 3 = { num := 1, denMinusOne := 2 } := by
  rfl

theorem rawUnitFraction_five_value :
    rawUnitFraction 5 = { num := 1, denMinusOne := 4 } := by
  rfl

theorem rawUnitFraction_seven_value :
    rawUnitFraction 7 = { num := 1, denMinusOne := 6 } := by
  rfl

theorem clausePrimeCandidates_one :
    clausePrimeCandidates 1 = [2, 3] := by
  rfl

theorem clausePrimeCandidates_two :
    clausePrimeCandidates 2 = [2, 3, 5] := by
  rfl

theorem clausePrimeCandidates_three :
    clausePrimeCandidates 3 = [2, 3, 7] := by
  rfl

theorem clauseDenominatorProductNat_one :
    clauseDenominatorProductNat 1 = 6 := by
  rfl

theorem clauseDenominatorProductNat_two :
    clauseDenominatorProductNat 2 = 30 := by
  rfl

theorem clauseDenominatorProductNat_three :
    clauseDenominatorProductNat 3 = 42 := by
  rfl

theorem rawBernoulliDenominator_two :
    rawBernoulliDenominator 2 = 6 := by
  rfl

theorem rawBernoulliDenominator_four :
    rawBernoulliDenominator 4 = 30 := by
  rfl

theorem rawBernoulliDenominator_six :
    rawBernoulliDenominator 6 = 42 := by
  rfl

theorem rawBernoulli_two_denominator_matches_clausen :
    rawBernoulliDenominatorMatchesClausenAt 1 := by
  rfl

theorem rawBernoulli_four_denominator_matches_clausen :
    rawBernoulliDenominatorMatchesClausenAt 2 := by
  rfl

theorem rawBernoulli_six_denominator_matches_clausen :
    rawBernoulliDenominatorMatchesClausenAt 3 := by
  rfl

theorem bernoulli_two_denominator_matches_clausen :
    bernoulliDenominatorMatchesClausenAt 1 := by
  rfl

theorem bernoulli_four_denominator_matches_clausen :
    bernoulliDenominatorMatchesClausenAt 2 := by
  rfl

theorem bernoulli_six_denominator_matches_clausen :
    bernoulliDenominatorMatchesClausenAt 3 := by
  rfl

def bernoulliSix : RatNum :=
  ratOfIntOverNat 1 41

theorem bernoulli_two_value :
    RatEq (bernoulli 2) bernoulliTwo :=
  BernoulliUp.bernoulli_two

theorem bernoulli_four_value :
    RatEq (bernoulli 4) bernoulliFour :=
  BernoulliUp.bernoulli_four

theorem bernoulli_six :
    RatEq (bernoulli 6) bernoulliSix := by
  simpa [bernoulli, bernoulliSix, ratOfIntOverNat, rawBernoulli_six_value]
    using RatEq_refl bernoulliSix

theorem rawClausenSum_one_value :
    rawClausenSum 1 (clausePrimeCandidates 1) =
      { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawClausenSum_two_value :
    rawClausenSum 2 (clausePrimeCandidates 2) =
      { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawClausenSum_three_value :
    rawClausenSum 3 (clausePrimeCandidates 3) =
      { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawVonStaudtClausenIntegral_one :
    rawVonStaudtClausenIntegralAt 1 := by
  rfl

theorem rawVonStaudtClausenIntegral_two :
    rawVonStaudtClausenIntegralAt 2 := by
  rfl

theorem rawVonStaudtClausenIntegral_three :
    rawVonStaudtClausenIntegralAt 3 := by
  rfl

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem NatTwo_prime : NatPrime NatTwo := by
  have large : NatUnaryStrictPrefix NatOne NatTwo :=
    natOne_strict_natToUnary_succ_succ 0
  change NatPrime (minFactor NatTwo large)
  exact minFactor_prime large

theorem NatThree_prime : NatPrime NatThree := by
  have large : NatUnaryStrictPrefix NatOne NatThree :=
    natOne_strict_natToUnary_succ_succ 1
  change NatPrime (minFactor NatThree large)
  exact minFactor_prime large

theorem NatFive_prime : NatPrime NatFive := by
  have large : NatUnaryStrictPrefix NatOne NatFive :=
    natOne_strict_natToUnary_succ_succ 3
  change NatPrime (minFactor NatFive large)
  exact minFactor_prime large

theorem NatSeven_prime : NatPrime NatSeven := by
  have large : NatUnaryStrictPrefix NatOne NatSeven :=
    natOne_strict_natToUnary_succ_succ 5
  change NatPrime (minFactor NatSeven large)
  exact minFactor_prime large

def clausePrimeHistCandidates (n : Nat) : List BHist :=
  (clausePrimeCandidates n).map natToUnary

def histProduct : List BHist -> BHist
  | [] => NatOne
  | p :: ps => natMulFn p (histProduct ps)

theorem clausePrimeHistCandidates_one :
    clausePrimeHistCandidates 1 = [NatTwo, NatThree] := by
  rfl

theorem clausePrimeHistCandidates_two :
    clausePrimeHistCandidates 2 = [NatTwo, NatThree, NatFive] := by
  rfl

theorem clausePrimeHistCandidates_three :
    clausePrimeHistCandidates 3 = [NatTwo, NatThree, NatSeven] := by
  rfl

theorem clausePrimeHistCandidates_one_all_prime :
    ∀ p : BHist, p ∈ clausePrimeHistCandidates 1 -> NatPrime p := by
  intro p member
  rw [clausePrimeHistCandidates_one] at member
  cases member with
  | head =>
      exact NatTwo_prime
  | tail _ memberTail =>
      cases memberTail with
      | head =>
          exact NatThree_prime
      | tail _ impossible =>
          cases impossible

theorem clausePrimeHistCandidates_two_all_prime :
    ∀ p : BHist, p ∈ clausePrimeHistCandidates 2 -> NatPrime p := by
  intro p member
  rw [clausePrimeHistCandidates_two] at member
  cases member with
  | head =>
      exact NatTwo_prime
  | tail _ memberTail =>
      cases memberTail with
      | head =>
          exact NatThree_prime
      | tail _ memberTailTail =>
          cases memberTailTail with
          | head =>
              exact NatFive_prime
          | tail _ impossible =>
              cases impossible

theorem clausePrimeHistCandidates_three_all_prime :
    ∀ p : BHist, p ∈ clausePrimeHistCandidates 3 -> NatPrime p := by
  intro p member
  rw [clausePrimeHistCandidates_three] at member
  cases member with
  | head =>
      exact NatTwo_prime
  | tail _ memberTail =>
      cases memberTail with
      | head =>
          exact NatThree_prime
      | tail _ memberTailTail =>
          cases memberTailTail with
          | head =>
              exact NatSeven_prime
          | tail _ impossible =>
              cases impossible

theorem histProduct_one :
    hsame (histProduct (clausePrimeHistCandidates 1)) NatSix := by
  rfl

theorem histProduct_two :
    hsame (histProduct (clausePrimeHistCandidates 2)) NatThirty := by
  rfl

theorem histProduct_three :
    hsame (histProduct (clausePrimeHistCandidates 3)) NatFortyTwo := by
  rfl

theorem clauseHistProduct_matches_denominator_one :
    hsame (histProduct (clausePrimeHistCandidates 1)) (bernoulliDenominator 2) := by
  rfl

theorem clauseHistProduct_matches_denominator_two :
    hsame (histProduct (clausePrimeHistCandidates 2)) (bernoulliDenominator 4) := by
  rfl

theorem clauseHistProduct_matches_denominator_three :
    hsame (histProduct (clausePrimeHistCandidates 3)) (bernoulliDenominator 6) := by
  rfl

theorem small_vonStaudtClausen_denominator_window :
    rawVonStaudtClausenIntegralAt 1 ∧
      rawBernoulliDenominatorMatchesClausenAt 1 ∧
      rawVonStaudtClausenIntegralAt 2 ∧
      rawBernoulliDenominatorMatchesClausenAt 2 ∧
      rawVonStaudtClausenIntegralAt 3 ∧
      rawBernoulliDenominatorMatchesClausenAt 3 := by
  exact ⟨rawVonStaudtClausenIntegral_one,
    rawBernoulli_two_denominator_matches_clausen,
    rawVonStaudtClausenIntegral_two,
    rawBernoulli_four_denominator_matches_clausen,
    rawVonStaudtClausenIntegral_three,
    rawBernoulli_six_denominator_matches_clausen⟩

end BEDC.Derived.VonStaudtClausenUp
