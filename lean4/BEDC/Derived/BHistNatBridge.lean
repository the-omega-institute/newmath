import BEDC.Derived.FermatLittleUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.BHistNatBridge

open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.FermatWilsonUp

abbrev bhistToNat (h : BHist) : Nat :=
  bwordLength h

abbrev natToBHist (n : Nat) : BHist :=
  natToUnary n

abbrev NatOneHist : BHist :=
  BHist.e1 BHist.Empty

theorem natToBHist_unary (n : Nat) : UnaryHistory (natToBHist n) := by
  exact natToUnary_unary n

theorem bhistToNat_empty :
    bhistToNat BHist.Empty = 0 := by
  rfl

theorem bhistToNat_e1 (h : BHist) :
    bhistToNat (BHist.e1 h) = Nat.succ (bhistToNat h) := by
  rfl

theorem bhistToNat_natToBHist (n : Nat) :
    bhistToNat (natToBHist n) = n := by
  exact natToUnary_length n

theorem natToBHist_bhistToNat {h : BHist} :
    UnaryHistory h -> hsame (natToBHist (bhistToNat h)) h := by
  intro hUnary
  exact (NatUp_unary_standard_bridge.right.right.right.left
    (natToBHist_unary (bhistToNat h)) hUnary).mpr (by
      exact bhistToNat_natToBHist (bhistToNat h))

theorem bhistToNat_hsame {h k : BHist} :
    hsame h k -> bhistToNat h = bhistToNat k := by
  intro same
  cases same
  rfl

theorem hsame_of_bhistToNat_eq {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bhistToNat h = bhistToNat k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

theorem natToBHist_append (m n : Nat) :
    append (natToBHist m) (natToBHist n) = natToBHist (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToBHist m) (natToBHist n)) =
        natToBHist (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem natToBHist_add_rel (m n : Nat) :
    NatAdd (natToBHist m) (natToBHist n) (natToBHist (m + n)) := by
  exact ⟨natToBHist_unary m, natToBHist_unary n,
    cont_intro (natToBHist_append m n).symm⟩

theorem bhistToNat_add {m n s : BHist} :
    NatAdd m n s -> bhistToNat s = bhistToNat m + bhistToNat n := by
  intro add
  exact NatAdd_length add

theorem natToBHist_mul_rel (a b : Nat) :
    NatMul (natToBHist a) (natToBHist b) (natToBHist (a * b)) := by
  have total := NatMul_total (natToBHist_unary a) (natToBHist_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToBHist (a * b)) :=
        hsame_of_bhistToNat_eq resultData.left (natToBHist_unary (a * b)) (by
          calc
            bhistToNat result =
                bhistToNat (natToBHist a) * bhistToNat (natToBHist b) :=
              NatMul_bwordLength resultData.right
            _ = a * b := by
              rw [bhistToNat_natToBHist, bhistToNat_natToBHist]
            _ = bhistToNat (natToBHist (a * b)) :=
              (bhistToNat_natToBHist (a * b)).symm)
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem bhistToNat_mul {d q n : BHist} :
    NatMul d q n -> bhistToNat n = bhistToNat d * bhistToNat q := by
  intro mul
  exact NatMul_bwordLength mul

def bhistPow (a : BHist) : Nat -> BHist
  | 0 => NatOneHist
  | exponent + 1 => natMulFn (bhistPow a exponent) a

def natPowStd (a : Nat) : Nat -> Nat
  | 0 => 1
  | exponent + 1 => natPowStd a exponent * a

theorem bhistPow_unary {a : BHist} :
    UnaryHistory a -> ∀ exponent : Nat, UnaryHistory (bhistPow a exponent)
  | _aUnary, 0 =>
      unary_e1_closed unary_empty
  | aUnary, exponent + 1 =>
      natMulFn_unary (bhistPow_unary aUnary exponent) aUnary

theorem bhistToNat_pow {a : BHist} :
    UnaryHistory a -> ∀ exponent : Nat,
      bhistToNat (bhistPow a exponent) = natPowStd (bhistToNat a) exponent
  | _aUnary, 0 =>
      rfl
  | aUnary, exponent + 1 => by
      change bhistToNat (natMulFn (bhistPow a exponent) a) =
        natPowStd (bhistToNat a) exponent * bhistToNat a
      calc
        bhistToNat (natMulFn (bhistPow a exponent) a) =
            bhistToNat (bhistPow a exponent) * bhistToNat a :=
          natMulFn_bwordLength (bhistPow_unary aUnary exponent) aUnary
        _ = natPowStd (bhistToNat a) exponent * bhistToNat a :=
          congrArg (fun n => n * bhistToNat a) (bhistToNat_pow aUnary exponent)

theorem bhistPow_natToBHist_hsame (a exponent : Nat) :
    hsame (bhistPow (natToBHist a) exponent)
      (natToBHist (natPowStd a exponent)) := by
  apply hsame_of_bhistToNat_eq
  · exact bhistPow_unary (natToBHist_unary a) exponent
  · exact natToBHist_unary (natPowStd a exponent)
  · rw [bhistToNat_pow (natToBHist_unary a) exponent]
    rw [bhistToNat_natToBHist a]
    exact (bhistToNat_natToBHist (natPowStd a exponent)).symm

theorem natPowStd_eq_pow (a exponent : Nat) :
    natPowStd a exponent = a ^ exponent := by
  induction exponent with
  | zero =>
      rfl
  | succ exponent ih =>
      change natPowStd a exponent * a = a ^ Nat.succ exponent
      rw [ih, Nat.pow_succ]

theorem zmodPowNat_val_bhistPow {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a) :
    ∀ exponent : Nat,
      hsame
        (zmodPowNat prime
          (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
          exponent).val
        (natModFn p (bhistPow a exponent))
  | 0 =>
      rfl
  | exponent + 1 => by
      let aMod : ZMod p :=
        zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary
      change hsame
        (natModFn p
          (natMulFn
            (zmodPowNat prime
              (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
              exponent).val
            (natModFn p a)))
        (natModFn p (natMulFn (bhistPow a exponent) a))
      have powUnary : UnaryHistory (bhistPow a exponent) :=
        bhistPow_unary aUnary exponent
      have remPowUnary : UnaryHistory (natModFn p (bhistPow a exponent)) :=
        natModFn_unary prime.left powUnary (NatPrime_empty_absurd prime)
      have remAUnary : UnaryHistory (natModFn p a) :=
        natModFn_unary prime.left aUnary (NatPrime_empty_absurd prime)
      have stepToReduced :
          hsame
            (natModFn p
              (natMulFn
                (zmodPowNat prime
                  (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
                  exponent).val
                (natModFn p a)))
            (natModFn p
              (natMulFn (natModFn p (bhistPow a exponent)) (natModFn p a))) :=
        natModFn_hsame_arg_transport (M := p)
          (natMulFn_hsame_transport
            (zmodPowNat_val_bhistPow prime aUnary exponent) (hsame_refl _))
      have rawToReduced :
          hsame
            (natModFn p (natMulFn (bhistPow a exponent) a))
            (natModFn p
              (natMulFn (natModFn p (bhistPow a exponent)) (natModFn p a))) :=
        mod_mul_compat prime.left (NatPrime_empty_absurd prime) powUnary aUnary
      exact hsame_trans stepToReduced (hsame_symm rawToReduced)

theorem fermatLittle_natModFn_transport {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a) :
    hsame
      (natModFn p (bhistPow a (bhistToNat p)))
      (natModFn p a) := by
  have powVal :=
    zmodPowNat_val_bhistPow prime aUnary (bhistToNat p)
  have fermat :=
    BEDC.Derived.FermatLittleUp.fermatLittle_all prime aUnary
  exact hsame_trans (hsame_symm powVal) fermat

def StdNatDivides (d n : Nat) : Prop :=
  ∃ q : Nat, n = d * q

theorem natDivides_to_std {d n : BHist} :
    NatDivides d n -> StdNatDivides (bhistToNat d) (bhistToNat n) := by
  intro divides
  cases divides with
  | intro q qData =>
      exact ⟨bhistToNat q, bhistToNat_mul qData.right⟩

theorem stdDivides_to_natToBHist_divides {d n : Nat} :
    StdNatDivides d n -> NatDivides (natToBHist d) (natToBHist n) := by
  intro divides
  cases divides with
  | intro q eqN =>
      cases eqN
      exact ⟨natToBHist q, natToBHist_unary q, natToBHist_mul_rel d q⟩

def StdNatPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, StdNatDivides d p -> d = 1 ∨ d = p

theorem natPrime_to_standard_prime {p : BHist} :
    NatPrime p -> StdNatPrime (bhistToNat p) := by
  intro prime
  constructor
  · have unitLt := NatUnaryStrictPrefix_length_lt
      (unary_e1_closed unary_empty) prime.right.left
    change 1 < bhistToNat p
    exact unitLt
  · intro d dividesD
    have dividesHist : NatDivides (natToBHist d) p := by
      have lifted := stdDivides_to_natToBHist_divides dividesD
      have sameP := natToBHist_bhistToNat prime.left
      exact (NatDivides_dividend_hsame_transport lifted sameP).right
    have divisorCases :=
      prime.right.right (natToBHist d) (natToBHist_unary d) dividesHist
    cases divisorCases with
    | inl unit =>
        left
        have lengthEq := congrArg bhistToNat unit
        simpa [natToBHist, bhistToNat, NatOneHist, natToUnary_length] using lengthEq
    | inr self =>
        right
        have lengthEq := congrArg bhistToNat self
        simpa [natToBHist, bhistToNat, natToUnary_length] using lengthEq

theorem NatUnaryStrictPrefix_of_bhistToNat_lt {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bhistToNat h < bhistToNat k ->
      NatUnaryStrictPrefix h k := by
  intro hUnary kUnary lengthLt
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl left =>
      cases left with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bhistToNat h = bhistToNat k := bhistToNat_hsame same
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strict =>
              exact strict
  | inr right =>
      cases right with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bhistToNat h = bhistToNat k :=
                bhistToNat_hsame (hsame_symm same)
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strictKH =>
              have kLtH := NatUnaryStrictPrefix_length_lt kUnary strictKH
              exact False.elim (Nat.lt_asymm lengthLt kLtH)

theorem standard_prime_to_natPrime {p : BHist} :
    UnaryHistory p -> StdNatPrime (bhistToNat p) -> NatPrime p := by
  intro pUnary stdPrime
  constructor
  · exact pUnary
  · constructor
    · exact NatUnaryStrictPrefix_of_bhistToNat_lt
        (unary_e1_closed unary_empty) pUnary stdPrime.left
    · intro d dUnary divides
      have stdDivides := natDivides_to_std divides
      have dCases := stdPrime.right (bhistToNat d) stdDivides
      cases dCases with
      | inl unitLength =>
          left
          exact hsame_of_bhistToNat_eq dUnary (unary_e1_closed unary_empty) unitLength
      | inr pLength =>
          right
          exact hsame_of_bhistToNat_eq dUnary pUnary pLength

theorem natPrime_iff_standard_prime_on_unary {p : BHist} :
    UnaryHistory p -> (NatPrime p ↔ StdNatPrime (bhistToNat p)) := by
  intro pUnary
  constructor
  · exact natPrime_to_standard_prime
  · exact standard_prime_to_natPrime pUnary

def NatFermatCongruence (p a : Nat) : Prop :=
  a ^ p % p = a % p

theorem stdNatPrime_two : StdNatPrime 2 := by
  change StdNatPrime (bhistToNat (BHist.e1 (BHist.e1 BHist.Empty)))
  exact natPrime_to_standard_prime NatPrime_first_pair.left

theorem stdNatPrime_three : StdNatPrime 3 := by
  change StdNatPrime (bhistToNat (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty))))
  exact natPrime_to_standard_prime NatPrime_first_pair.right

theorem fermatLittle_nat_sample_two_three :
    NatFermatCongruence 3 2 := by
  unfold NatFermatCongruence
  rfl

theorem exported_nat_fermat_sample_two_three :
    StdNatPrime 3 ∧ NatFermatCongruence 3 2 := by
  exact ⟨stdNatPrime_three, fermatLittle_nat_sample_two_three⟩

end BEDC.Derived.BHistNatBridge
