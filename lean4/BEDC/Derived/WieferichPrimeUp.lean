import BEDC.Derived.FermatLittleUp
import BEDC.Derived.PadicUp.ExactDivision
import BEDC.Derived.PrimeUp.PrimeShape
import BEDC.Derived.PrimeUp.UniqueFactorization

set_option maxRecDepth 20000
set_option exponentiation.threshold 4000
set_option maxHeartbeats 2000000

namespace BEDC.Derived.WieferichPrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne

def natPowFn (base : BHist) : Nat -> BHist
  | 0 => NatOne
  | k + 1 => natMulFn base (natPowFn base k)

theorem natPowFn_unary {base : BHist} :
    UnaryHistory base -> ∀ k : Nat, UnaryHistory (natPowFn base k)
  | _baseUnary, 0 => unary_e1_closed unary_empty
  | baseUnary, k + 1 => natMulFn_unary baseUnary (natPowFn_unary baseUnary k)

def fermatNumeratorHist (base p : BHist) : BHist :=
  natSubUnary (natPowFn base (bwordLength p - 1)) NatOne

theorem fermatNumeratorHist_unary {base p : BHist} :
    UnaryHistory base -> UnaryHistory (fermatNumeratorHist base p) := by
  intro baseUnary
  unfold fermatNumeratorHist
  exact natSubUnary_unary (natPowFn_unary baseUnary (bwordLength p - 1))

def fermatQuotientHist (base p : BHist) : BHist :=
  natQuotFn p (fermatNumeratorHist base p)

theorem fermatQuotientHist_unary {base p : BHist} :
    UnaryHistory base -> UnaryHistory p -> (hsame p BHist.Empty -> False) ->
      UnaryHistory (fermatQuotientHist base p) := by
  intro baseUnary pUnary pNonempty
  unfold fermatQuotientHist
  exact natQuotFn_unary pUnary (fermatNumeratorHist_unary baseUnary) pNonempty

def fermatQuotientVanishHist (base p : BHist) : Prop :=
  hsame (natModFn p (fermatQuotientHist base p)) BHist.Empty

def fermatSpecialHist (base p : BHist) : Prop :=
  hsame (natModFn p (natPowFn base (bwordLength p - 1))) (natModFn p NatOne)

def wieferichCongruenceHist (base p : BHist) : Prop :=
  hsame
    (natModFn (natMulFn p p) (natPowFn base (bwordLength p - 1)))
    (natModFn (natMulFn p p) NatOne)

structure WieferichWitnessHist (base p : BHist) where
  square_congruence : wieferichCongruenceHist base p
  fermat_quotient_vanishes : fermatQuotientVanishHist base p
  fermat_special : fermatSpecialHist base p

def WieferichPrimeHist (p : BHist) : Prop :=
  NatPrime p ∧ Nonempty (WieferichWitnessHist NatTwo p)

theorem fermatQuotientVanishHist_divides_quotient {base p : BHist} :
    UnaryHistory base -> UnaryHistory p -> (hsame p BHist.Empty -> False) ->
      fermatQuotientVanishHist base p -> NatDivides p (fermatQuotientHist base p) := by
  intro baseUnary pUnary pNonempty vanish
  exact (dvd_iff_mod_zero pUnary pNonempty
    (fermatQuotientHist_unary baseUnary pUnary pNonempty)).mpr vanish

theorem WieferichWitnessHist.fermat_quotient_divides {base p : BHist} :
    UnaryHistory base -> UnaryHistory p -> (hsame p BHist.Empty -> False) ->
      WieferichWitnessHist base p -> NatDivides p (fermatQuotientHist base p) := by
  intro baseUnary pUnary pNonempty witness
  exact fermatQuotientVanishHist_divides_quotient baseUnary pUnary pNonempty
    witness.fermat_quotient_vanishes

private theorem NatTwo_unary : UnaryHistory NatTwo :=
  unary_e1_closed (unary_e1_closed unary_empty)

theorem WieferichPrimeHist.fermat_quotient_divides {p : BHist} :
    WieferichPrimeHist p -> NatDivides p (fermatQuotientHist NatTwo p) := by
  intro witness
  cases witness.right with
  | intro data =>
      exact WieferichWitnessHist.fermat_quotient_divides NatTwo_unary
        witness.left.left (NatPrime_empty_absurd witness.left) data

def fermatQuotientNat (base p : Nat) : Nat :=
  (base ^ (p - 1) - 1) / p

def fermatQuotientVanishBool (base p : Nat) : Bool :=
  Nat.beq (fermatQuotientNat base p % p) 0

def fermatSpecialBool (base p : Nat) : Bool :=
  Nat.beq (base ^ (p - 1) % p) (1 % p)

def wieferichCongruenceBool (base p : Nat) : Bool :=
  Nat.beq (base ^ (p - 1) % (p * p)) (1 % (p * p))

structure WieferichWitnessNat (base p : Nat) where
  square_congruence : wieferichCongruenceBool base p = true
  fermat_quotient_vanishes : fermatQuotientVanishBool base p = true
  fermat_special : fermatSpecialBool base p = true

def WieferichPrimeNat (p : Nat) : Prop :=
  NatPrime (natToUnary p) ∧ Nonempty (WieferichWitnessNat 2 p)

def WieferichVerifiedNat (p : Nat) : Prop :=
  Nonempty (WieferichWitnessNat 2 p)

theorem wieferich_1093_square_congruence :
    wieferichCongruenceBool 2 1093 = true := by
  decide

theorem wieferich_1093_fermat_quotient_vanishes :
    fermatQuotientVanishBool 2 1093 = true := by
  decide

theorem wieferich_1093_fermat_special :
    fermatSpecialBool 2 1093 = true := by
  decide

theorem wieferich_3511_square_congruence :
    wieferichCongruenceBool 2 3511 = true := by
  decide

theorem wieferich_3511_fermat_quotient_vanishes :
    fermatQuotientVanishBool 2 3511 = true := by
  decide

theorem wieferich_3511_fermat_special :
    fermatSpecialBool 2 3511 = true := by
  decide

def wieferich1093Witness : WieferichWitnessNat 2 1093 where
  square_congruence := wieferich_1093_square_congruence
  fermat_quotient_vanishes := wieferich_1093_fermat_quotient_vanishes
  fermat_special := wieferich_1093_fermat_special

def wieferich3511Witness : WieferichWitnessNat 2 3511 where
  square_congruence := wieferich_3511_square_congruence
  fermat_quotient_vanishes := wieferich_3511_fermat_quotient_vanishes
  fermat_special := wieferich_3511_fermat_special

theorem WieferichVerifiedNat_1093 : WieferichVerifiedNat 1093 := by
  exact ⟨wieferich1093Witness⟩

theorem WieferichVerifiedNat_3511 : WieferichVerifiedNat 3511 := by
  exact ⟨wieferich3511Witness⟩

theorem WieferichPrimeNat.prime {p : Nat} :
    WieferichPrimeNat p -> NatPrime (natToUnary p) := by
  intro witness
  exact witness.left

theorem WieferichPrimeNat.square_congruence {p : Nat} :
    WieferichPrimeNat p -> wieferichCongruenceBool 2 p = true := by
  intro witness
  cases witness.right with
  | intro data =>
      exact data.square_congruence

theorem WieferichPrimeNat.fermat_quotient_vanishes {p : Nat} :
    WieferichPrimeNat p -> fermatQuotientVanishBool 2 p = true := by
  intro witness
  cases witness.right with
  | intro data =>
      exact data.fermat_quotient_vanishes

theorem WieferichPrimeNat.fermat_special {p : Nat} :
    WieferichPrimeNat p -> fermatSpecialBool 2 p = true := by
  intro witness
  cases witness.right with
  | intro data =>
      exact data.fermat_special

theorem WieferichVerifiedNat.square_congruence {p : Nat} :
    WieferichVerifiedNat p -> wieferichCongruenceBool 2 p = true := by
  intro witness
  cases witness with
  | intro data =>
      exact data.square_congruence

theorem WieferichVerifiedNat.fermat_quotient_vanishes {p : Nat} :
    WieferichVerifiedNat p -> fermatQuotientVanishBool 2 p = true := by
  intro witness
  cases witness with
  | intro data =>
      exact data.fermat_quotient_vanishes

theorem WieferichVerifiedNat.fermat_special {p : Nat} :
    WieferichVerifiedNat p -> fermatSpecialBool 2 p = true := by
  intro witness
  cases witness with
  | intro data =>
      exact data.fermat_special

end BEDC.Derived.WieferichPrimeUp
