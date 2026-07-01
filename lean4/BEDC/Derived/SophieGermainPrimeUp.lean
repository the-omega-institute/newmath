import BEDC.Derived.PrattCertificateUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.SophieGermainPrimeUp

open BEDC.FKernel.Hist
open BEDC.Derived.IntUp (natToUnary)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def sophieGermainCandidateNat (p : Nat) : Nat :=
  2 * p + 1

def SophieGermainPrimePair (p q : BHist) : Prop :=
  NatPrime p ∧ NatPrime q ∧
    ∃ double : BHist, NatAdd p p double ∧ NatAdd double (natToUnary 1) q

def SophieGermainPrimeNat (p : Nat) : Prop :=
  SophieGermainPrimePair (natToUnary p) (natToUnary (sophieGermainCandidateNat p))

theorem sophieGermainCandidate_zero :
    sophieGermainCandidateNat 0 = 1 := by
  rfl

theorem sophieGermainCandidate_succ (p : Nat) :
    sophieGermainCandidateNat (Nat.succ p) =
      sophieGermainCandidateNat p + 2 := by
  unfold sophieGermainCandidateNat
  rw [Nat.mul_succ]

theorem sophieGermainCandidate_two :
    sophieGermainCandidateNat 2 = 5 := by
  rfl

theorem sophieGermainCandidate_three :
    sophieGermainCandidateNat 3 = 7 := by
  rfl

theorem sophieGermainPrimePair_two_five :
    SophieGermainPrimePair (natToUnary 2) (natToUnary 5) := by
  constructor
  · exact BEDC.Derived.PrattCertificateUp.pratt_certificate_two_prime
  · constructor
    · exact BEDC.Derived.PrattCertificateUp.pratt_certificate_five_prime
    · exact ⟨natToUnary 4,
        BEDC.Derived.StirlingUp.natToUnary_add_rel 2 2,
        BEDC.Derived.StirlingUp.natToUnary_add_rel 4 1⟩

theorem sophieGermainPrimeNat_two :
    SophieGermainPrimeNat 2 := by
  unfold SophieGermainPrimeNat
  exact sophieGermainPrimePair_two_five

theorem sophieGermainPrimePair_left_prime {p q : BHist} :
    SophieGermainPrimePair p q -> NatPrime p := by
  intro h
  exact h.left

theorem sophieGermainPrimePair_candidate_prime {p q : BHist} :
    SophieGermainPrimePair p q -> NatPrime q := by
  intro h
  exact h.right.left

theorem SophieGermainPrimeUp_constructive_export :
    sophieGermainCandidateNat 2 = 5 ∧
      sophieGermainCandidateNat 3 = 7 ∧
      SophieGermainPrimeNat 2 ∧
      (∀ p q : BHist, SophieGermainPrimePair p q -> NatPrime p ∧ NatPrime q) := by
  constructor
  · exact sophieGermainCandidate_two
  · constructor
    · exact sophieGermainCandidate_three
    · constructor
      · exact sophieGermainPrimeNat_two
      · intro p q h
        exact ⟨sophieGermainPrimePair_left_prime h,
          sophieGermainPrimePair_candidate_prime h⟩

end BEDC.Derived.SophieGermainPrimeUp
