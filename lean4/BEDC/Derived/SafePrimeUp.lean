import BEDC.Derived.PrattCertificateUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.SafePrimeUp

open BEDC.FKernel.Hist
open BEDC.Derived.IntUp (natToUnary)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def safePrimeCandidateNat (q : Nat) : Nat :=
  2 * q + 1

def SafePrimePair (p q : BHist) : Prop :=
  NatPrime p ∧ NatPrime q ∧
    ∃ double : BHist, NatAdd q q double ∧ NatAdd double (natToUnary 1) p

def SafePrimeNat (p q : Nat) : Prop :=
  SafePrimePair (natToUnary p) (natToUnary q)

theorem safePrimeCandidate_two :
    safePrimeCandidateNat 2 = 5 := by
  rfl

theorem safePrimeCandidate_three :
    safePrimeCandidateNat 3 = 7 := by
  rfl

theorem safePrimePair_five_two :
    SafePrimePair (natToUnary 5) (natToUnary 2) := by
  constructor
  · exact BEDC.Derived.PrattCertificateUp.pratt_certificate_five_prime
  · constructor
    · exact BEDC.Derived.PrattCertificateUp.pratt_certificate_two_prime
    · exact ⟨natToUnary 4,
        BEDC.Derived.StirlingUp.natToUnary_add_rel 2 2,
        BEDC.Derived.StirlingUp.natToUnary_add_rel 4 1⟩

theorem safePrimeNat_five_two :
    SafePrimeNat 5 2 := by
  unfold SafePrimeNat
  exact safePrimePair_five_two

theorem safePrimePair_prime {p q : BHist} :
    SafePrimePair p q -> NatPrime p := by
  intro h
  exact h.left

theorem safePrimePair_sophie_factor_prime {p q : BHist} :
    SafePrimePair p q -> NatPrime q := by
  intro h
  exact h.right.left

theorem SafePrimeUp_constructive_export :
    safePrimeCandidateNat 2 = 5 ∧
      safePrimeCandidateNat 3 = 7 ∧
      SafePrimeNat 5 2 ∧
      (∀ p q : BHist, SafePrimePair p q -> NatPrime p ∧ NatPrime q) := by
  constructor
  · exact safePrimeCandidate_two
  · constructor
    · exact safePrimeCandidate_three
    · constructor
      · exact safePrimeNat_five_two
      · intro p q h
        exact ⟨safePrimePair_prime h, safePrimePair_sophie_factor_prime h⟩

end BEDC.Derived.SafePrimeUp
