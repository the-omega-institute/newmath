import BEDC.Derived.WilsonTheoremUp
import BEDC.Derived.PadicUp.ExactDivision

namespace BEDC.Derived.WilsonQuotientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.WilsonUp
open BEDC.Derived.ZModUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne
abbrev NatThree : BHist := BHist.e1 NatTwo
abbrev NatFour : BHist := BHist.e1 NatThree
abbrev NatFive : BHist := BHist.e1 NatFour

def wilsonNumerator (p : BHist) : BHist :=
  append (natFactorialFn (primePred p)) NatOne

def wilsonQuotient (p : BHist) : BHist :=
  natQuotFn p (wilsonNumerator p)

def WilsonCongruence (p : BHist) (prime : NatPrime p) : Prop :=
  zmodEq (wilsonFactorialResidue prime) (zmodMinusOne prime)

private theorem natOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

theorem wilsonNumerator_unary {p : BHist} (prime : NatPrime p) :
    UnaryHistory (wilsonNumerator p) := by
  unfold wilsonNumerator
  exact unary_append_closed
    (natFactorialFn_unary (primePred_unary prime))
    natOne_unary

private theorem neg_one_add_one_mod_zero {p : BHist} (prime : NatPrime p) :
    hsame
      (natModFn p
        (append
          (natComplementMod p (natModFn p NatOne))
          (natModFn p NatOne)))
      BHist.Empty := by
  have oneRemSame : hsame (natModFn p NatOne) NatOne :=
    natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
      natOne_unary prime.right.left
  have compSame :
      hsame (natComplementMod p (natModFn p NatOne))
        (natComplementMod p NatOne) :=
    natComplementMod_hsame_arg_transport oneRemSame
  have moved :
      hsame
        (natModFn p
          (append
            (natComplementMod p (natModFn p NatOne))
            (natModFn p NatOne)))
        (natModFn p
          (append (natComplementMod p NatOne) NatOne)) :=
    natModFn_append_hsame_transport compSame oneRemSame
  exact hsame_trans moved
    (natComplementMod_add_right_zero_of_strict prime.left
      (NatPrime_empty_absurd prime) natOne_unary prime.right.left)

theorem wilsonCongruence_mod_zero {p : BHist} (prime : NatPrime p) :
    WilsonCongruence p prime ->
      hsame (natModFn p (wilsonNumerator p)) BHist.Empty := by
  intro congruence
  unfold WilsonCongruence wilsonFactorialResidue zmodMinusOne zmodNeg zmodOne zmodEq at congruence
  unfold wilsonNumerator
  have oneUnary : UnaryHistory NatOne := natOne_unary
  have factorialUnary : UnaryHistory (natFactorialFn (primePred p)) :=
    natFactorialFn_unary (primePred_unary prime)
  have factorialModUnary : UnaryHistory (natModFn p (natFactorialFn (primePred p))) :=
    natModFn_unary prime.left factorialUnary (NatPrime_empty_absurd prime)
  have oneModUnary : UnaryHistory (natModFn p NatOne) :=
    natModFn_unary prime.left oneUnary (NatPrime_empty_absurd prime)
  have lifted :
      hsame
        (natModFn p
          (append
            (natModFn p (natFactorialFn (primePred p)))
            (natModFn p NatOne)))
        (natModFn p
          (append
            (natComplementMod p (natModFn p NatOne))
            (natModFn p NatOne))) :=
    natModFn_append_hsame_transport congruence (hsame_refl _)
  have rawToReduced :
      hsame
        (natModFn p
          (append (natFactorialFn (primePred p)) NatOne))
        (natModFn p
          (append
            (natModFn p (natFactorialFn (primePred p)))
            (natModFn p NatOne))) :=
    mod_add_compat prime.left (NatPrime_empty_absurd prime)
      factorialUnary oneUnary
  exact hsame_trans rawToReduced
    (hsame_trans lifted (neg_one_add_one_mod_zero prime))

theorem wilsonCongruence_divides_numerator {p : BHist} (prime : NatPrime p) :
    WilsonCongruence p prime ->
      NatDivides p (wilsonNumerator p) := by
  intro congruence
  exact (dvd_iff_mod_zero prime.left (NatPrime_empty_absurd prime)
    (wilsonNumerator_unary prime)).mpr
    (wilsonCongruence_mod_zero prime congruence)

theorem wilsonQuotient_exact {p : BHist} (prime : NatPrime p) :
    WilsonCongruence p prime ->
      hsame (natMulFn p (wilsonQuotient p)) (wilsonNumerator p) := by
  intro congruence
  unfold wilsonQuotient
  exact natDivRem_zero_recompose prime.left (wilsonNumerator_unary prime)
    (NatPrime_empty_absurd prime) (wilsonCongruence_mod_zero prime congruence)

theorem wilsonQuotient_integer {p : BHist} (prime : NatPrime p) :
    WilsonCongruence p prime ->
      NatDivides p (wilsonNumerator p) :=
  wilsonCongruence_divides_numerator prime

theorem wilsonQuotient_exact_from_standard_pairing_data {p : BHist}
    (prime : NatPrime p) (data : WilsonStandardPairingData p prime) :
    hsame (natMulFn p (wilsonQuotient p)) (wilsonNumerator p) := by
  exact wilsonQuotient_exact prime
    (WilsonTheoremUp.wilson_from_standard_pairing_data prime data)

theorem wilsonQuotient_integer_from_standard_pairing_data {p : BHist}
    (prime : NatPrime p) (data : WilsonStandardPairingData p prime) :
    NatDivides p (wilsonNumerator p) := by
  exact wilsonQuotient_integer prime
    (WilsonTheoremUp.wilson_from_standard_pairing_data prime data)

theorem wilsonQuotient_two_exact :
    hsame (natMulFn NatTwo (wilsonQuotient NatTwo)) (wilsonNumerator NatTwo) := by
  exact wilsonQuotient_exact NatPrime_first_pair.left
    WilsonTheoremUp.wilson_prime_two

theorem wilsonQuotient_three_exact :
    hsame (natMulFn NatThree (wilsonQuotient NatThree)) (wilsonNumerator NatThree) := by
  exact wilsonQuotient_exact NatPrime_first_pair.right
    WilsonTheoremUp.wilson_prime_three

theorem wilsonQuotient_five_exact :
    hsame (natMulFn NatFive (wilsonQuotient NatFive)) (wilsonNumerator NatFive) := by
  unfold wilsonQuotient wilsonNumerator NatFive NatFour NatThree NatTwo NatOne
    primePred natFactorialFn natQuotFn natMulFn
  rfl

theorem wilsonQuotient_two_value :
    hsame (wilsonQuotient NatTwo) NatOne := by
  unfold wilsonQuotient wilsonNumerator NatTwo NatOne primePred natFactorialFn natQuotFn
  rfl

theorem wilsonQuotient_three_value :
    hsame (wilsonQuotient NatThree) NatOne := by
  unfold wilsonQuotient wilsonNumerator NatThree NatTwo NatOne primePred natFactorialFn
  rfl

theorem wilsonQuotient_five_value :
    hsame (wilsonQuotient NatFive) NatFive := by
  unfold wilsonQuotient wilsonNumerator NatFive NatFour NatThree NatTwo NatOne
    primePred natFactorialFn natQuotFn
  rfl

end BEDC.Derived.WilsonQuotientUp
