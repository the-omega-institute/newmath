import BEDC.Derived.LucasTheoremBinomUp
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.PerrinUp

open BEDC.Derived.LucasTheoremBinomUp

private abbrev NatOne : BEDC.FKernel.Hist.BHist :=
  BEDC.Derived.PadicUp.NatOne

def perrin : Nat -> Nat
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | n + 3 => perrin (n + 1) + perrin n

def padovan : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n

def perrinUp (n : Nat) : BEDC.FKernel.Hist.BHist :=
  BEDC.Derived.IntUp.natToUnary (perrin n)

def WaveRecurrence (a : Nat -> Nat) : Prop :=
  ∀ n : Nat, a (n + 3) = a (n + 1) + a n

theorem perrin_zero :
    perrin 0 = 3 := by
  rfl

theorem perrin_one :
    perrin 1 = 0 := by
  rfl

theorem perrin_two :
    perrin 2 = 2 := by
  rfl

theorem perrin_recurrence (n : Nat) :
    perrin (n + 3) = perrin (n + 1) + perrin n := by
  rfl

theorem padovan_zero :
    padovan 0 = 1 := by
  rfl

theorem padovan_one :
    padovan 1 = 1 := by
  rfl

theorem padovan_two :
    padovan 2 = 1 := by
  rfl

theorem padovan_recurrence (n : Nat) :
    padovan (n + 3) = padovan (n + 1) + padovan n := by
  rfl

theorem perrin_padovan_same_wave :
    WaveRecurrence perrin ∧ WaveRecurrence padovan := by
  exact ⟨perrin_recurrence, padovan_recurrence⟩

theorem perrin_three :
    perrin 3 = 3 := by
  rfl

theorem perrin_four :
    perrin 4 = 2 := by
  rfl

theorem perrin_five :
    perrin 5 = 5 := by
  rfl

theorem perrin_six :
    perrin 6 = 5 := by
  rfl

theorem perrin_seven :
    perrin 7 = 7 := by
  rfl

theorem perrin_eight :
    perrin 8 = 10 := by
  rfl

theorem perrin_nine :
    perrin 9 = 12 := by
  rfl

theorem perrin_ten :
    perrin 10 = 17 := by
  rfl

theorem perrin_eleven :
    perrin 11 = 22 := by
  rfl

theorem perrin_thirteen :
    perrin 13 = 39 := by
  rfl

theorem perrin_seventeen :
    perrin 17 = 119 := by
  rfl

theorem perrinUp_unary (n : Nat) :
    BEDC.FKernel.Unary.UnaryHistory (perrinUp n) := by
  unfold perrinUp
  exact BEDC.Derived.IntUp.natToUnary_unary (perrin n)

theorem perrin_two_dvd :
    NatDvd 2 (perrin 2) := by
  change NatDvd 2 2
  exact NatDvd_of_factor (p := 2) (n := 2) (q := 1) rfl

theorem perrin_three_dvd :
    NatDvd 3 (perrin 3) := by
  change NatDvd 3 3
  exact NatDvd_of_factor (p := 3) (n := 3) (q := 1) rfl

theorem perrin_five_dvd :
    NatDvd 5 (perrin 5) := by
  change NatDvd 5 5
  exact NatDvd_of_factor (p := 5) (n := 5) (q := 1) rfl

theorem perrin_seven_dvd :
    NatDvd 7 (perrin 7) := by
  change NatDvd 7 7
  exact NatDvd_of_factor (p := 7) (n := 7) (q := 1) rfl

theorem perrin_eleven_dvd :
    NatDvd 11 (perrin 11) := by
  change NatDvd 11 22
  exact NatDvd_of_factor (p := 11) (n := 22) (q := 2) rfl

theorem perrin_thirteen_dvd :
    NatDvd 13 (perrin 13) := by
  change NatDvd 13 39
  exact NatDvd_of_factor (p := 13) (n := 39) (q := 3) rfl

theorem perrin_seventeen_dvd :
    NatDvd 17 (perrin 17) := by
  change NatDvd 17 119
  exact NatDvd_of_factor (p := 17) (n := 119) (q := 7) rfl

theorem perrin_two_prime :
    NatPrimeUp 2 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.NatPrime_first_pair.left

theorem perrin_three_prime :
    NatPrimeUp 3 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.NatPrime_first_pair.right

private theorem natOne_strict_of_tail (tail : BEDC.FKernel.Hist.BHist) :
    BEDC.FKernel.Unary.UnaryHistory tail -> (tail = BEDC.FKernel.Hist.BHist.Empty -> False) ->
      BEDC.Derived.NatUp.NatUnaryStrictPrefix NatOne (BEDC.FKernel.Hist.BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted :
      BEDC.FKernel.Cont.append NatOne tail = BEDC.FKernel.Hist.BHist.e1 tail :=
    (BEDC.FKernel.Unary.unary_append_e1_left
      (h := tail) (k := BEDC.FKernel.Hist.BHist.Empty) tailUnary).trans
        (congrArg BEDC.FKernel.Hist.BHist.e1
          (BEDC.FKernel.Cont.append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, BEDC.FKernel.Cont.cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    BEDC.Derived.NatUp.NatUnaryStrictPrefix NatOne
      (BEDC.Derived.IntUp.natToUnary (Nat.succ (Nat.succ n))) := by
  change BEDC.Derived.NatUp.NatUnaryStrictPrefix NatOne
    (BEDC.FKernel.Hist.BHist.e1 (BEDC.Derived.IntUp.natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (BEDC.Derived.IntUp.natToUnary (Nat.succ n))
    (BEDC.Derived.IntUp.natToUnary_unary (Nat.succ n)) (fun empty => by
      change BEDC.FKernel.Hist.BHist.e1 (BEDC.Derived.IntUp.natToUnary n) =
        BEDC.FKernel.Hist.BHist.Empty at empty
      exact BEDC.FKernel.Hist.not_hsame_e1_empty empty)

theorem perrin_five_prime :
    NatPrimeUp 5 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.minFactor_prime (natOne_strict_natToUnary_succ_succ 3)

theorem perrin_seven_prime :
    NatPrimeUp 7 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.minFactor_prime (natOne_strict_natToUnary_succ_succ 5)

theorem perrin_eleven_prime :
    NatPrimeUp 11 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.minFactor_prime (natOne_strict_natToUnary_succ_succ 9)

theorem perrin_thirteen_prime :
    NatPrimeUp 13 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.minFactor_prime (natOne_strict_natToUnary_succ_succ 11)

theorem perrin_seventeen_prime :
    NatPrimeUp 17 := by
  unfold NatPrimeUp
  exact BEDC.Derived.PrimeUp.minFactor_prime (natOne_strict_natToUnary_succ_succ 15)

theorem perrin_two_prime_dvd :
    NatPrimeUp 2 ∧ NatDvd 2 (perrin 2) := by
  exact ⟨perrin_two_prime, perrin_two_dvd⟩

theorem perrin_three_prime_dvd :
    NatPrimeUp 3 ∧ NatDvd 3 (perrin 3) := by
  exact ⟨perrin_three_prime, perrin_three_dvd⟩

theorem perrin_five_prime_dvd :
    NatPrimeUp 5 ∧ NatDvd 5 (perrin 5) := by
  exact ⟨perrin_five_prime, perrin_five_dvd⟩

theorem perrin_seven_prime_dvd :
    NatPrimeUp 7 ∧ NatDvd 7 (perrin 7) := by
  exact ⟨perrin_seven_prime, perrin_seven_dvd⟩

theorem perrin_eleven_prime_dvd :
    NatPrimeUp 11 ∧ NatDvd 11 (perrin 11) := by
  exact ⟨perrin_eleven_prime, perrin_eleven_dvd⟩

theorem perrin_thirteen_prime_dvd :
    NatPrimeUp 13 ∧ NatDvd 13 (perrin 13) := by
  exact ⟨perrin_thirteen_prime, perrin_thirteen_dvd⟩

theorem perrin_seventeen_prime_dvd :
    NatPrimeUp 17 ∧ NatDvd 17 (perrin 17) := by
  exact ⟨perrin_seventeen_prime, perrin_seventeen_dvd⟩

theorem prime_dvd_perrin_at_two_or_three {p : Nat} :
    p = 2 ∨ p = 3 -> NatPrimeUp p -> NatDvd p (perrin p) := by
  intro hp _prime
  cases hp with
  | inl h =>
      cases h
      exact perrin_two_dvd
  | inr h =>
      cases h
      exact perrin_three_dvd

theorem prime_dvd_perrin_small_prime_window {p : Nat} :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ->
      NatPrimeUp p -> NatDvd p (perrin p) := by
  intro hp _prime
  cases hp with
  | inl h =>
      cases h
      exact perrin_two_dvd
  | inr hp =>
      cases hp with
      | inl h =>
          cases h
          exact perrin_three_dvd
      | inr hp =>
          cases hp with
          | inl h =>
              cases h
              exact perrin_five_dvd
          | inr hp =>
              cases hp with
              | inl h =>
                  cases h
                  exact perrin_seven_dvd
              | inr hp =>
                  cases hp with
                  | inl h =>
                      cases h
                      exact perrin_eleven_dvd
                  | inr hp =>
                      cases hp with
                      | inl h =>
                          cases h
                          exact perrin_thirteen_dvd
                      | inr h =>
                          cases h
                          exact perrin_seventeen_dvd

theorem perrinUp_two_divides :
    BEDC.Derived.PrimeUp.NatDivides
      (BEDC.Derived.IntUp.natToUnary 2)
      (perrinUp 2) := by
  exact perrin_two_dvd

theorem perrinUp_three_divides :
    BEDC.Derived.PrimeUp.NatDivides
      (BEDC.Derived.IntUp.natToUnary 3)
      (perrinUp 3) := by
  exact perrin_three_dvd

end BEDC.Derived.PerrinUp
