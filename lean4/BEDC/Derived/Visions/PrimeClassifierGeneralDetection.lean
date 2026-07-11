import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# General finite residual detection core

This module keeps only the finite, kernel-checked layer of the prime-classifier
route.  Prime existence for an arbitrary finite support is represented by an
explicit residue certificate.  The divisibility fields record the intended
number-theoretic provenance, while the pure kernel consumes the residue facts
directly so that theorem dependencies remain axiom-free.
-/

namespace BEDC.Derived.Visions

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel

def pfzGeneralClassifierMod (p q : Nat) : Nat :=
  q % p

def pfzGeneralNatPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ a b : Nat, a * b = p -> a = 1 ∨ b = 1

def pfzGeneralSupportDistinctPositive (qs : List Nat) : Prop :=
  (∀ i : Fin qs.length, 0 < qs.get i) ∧
    ∀ i j : Fin qs.length, i ≠ j -> qs.get i ≠ qs.get j

def pfzGeneralResiduesNonzero (qs : List Nat) (p : Nat) : Prop :=
  ∀ i : Fin qs.length, pfzGeneralClassifierMod p (qs.get i) ≠ 0

def pfzGeneralResiduesInjectiveOnSupport (qs : List Nat) (p : Nat) : Prop :=
  ∀ i j : Fin qs.length, i ≠ j ->
    pfzGeneralClassifierMod p (qs.get i) ≠ pfzGeneralClassifierMod p (qs.get j)

def pfzGeneralFiniteSupportDetected (qs : List Nat) (p : Nat) : Prop :=
  pfzGeneralResiduesNonzero qs p ∧ pfzGeneralResiduesInjectiveOnSupport qs p

structure pfzGeneralPrimeModulusCertificate (qs : List Nat) (p : Nat) where
  prime : pfzGeneralNatPrime p
  support : pfzGeneralSupportDistinctPositive qs
  no_support_divisor : ∀ i : Fin qs.length, p ∣ qs.get i -> False
  no_ordered_difference_divisor :
    ∀ i j : Fin qs.length, i ≠ j -> qs.get j ≤ qs.get i ->
      p ∣ qs.get i - qs.get j -> False
  residue_nonzero : pfzGeneralResiduesNonzero qs p
  residue_injective : pfzGeneralResiduesInjectiveOnSupport qs p

theorem pfzGeneral_prime_modulus_positive {qs : List Nat} {p : Nat}
    (cert : pfzGeneralPrimeModulusCertificate qs p) :
    0 < p := by
  exact Nat.lt_trans (Nat.zero_lt_succ 0) cert.prime.left

theorem pfzGeneral_prime_modulus_certificate_detects
    {qs : List Nat} {p : Nat}
    (cert : pfzGeneralPrimeModulusCertificate qs p) :
    pfzGeneralFiniteSupportDetected qs p := by
  constructor
  · exact cert.residue_nonzero
  · exact cert.residue_injective

theorem pfzGeneral_exists_prime_modulus_injective_on_finite_support
    {qs : List Nat}
    (hcert : ∃ p : Nat, pfzGeneralPrimeModulusCertificate qs p) :
    ∃ p : Nat,
      pfzGeneralNatPrime p ∧ pfzGeneralSupportDistinctPositive qs ∧
        pfzGeneralFiniteSupportDetected qs p := by
  cases hcert with
  | intro p cert =>
      exact ⟨p, cert.prime, cert.support,
        pfzGeneral_prime_modulus_certificate_detects cert⟩

abbrev pfzGeneralResidual : Type :=
  List RatNum

def pfzGeneralRatNonzero (q : RatNum) : Prop :=
  RatEq q ratZero -> False

def pfzGeneralRatCoordinateDetected (q : RatNum) : Prop :=
  ratLt q ratZero ∨ ratLt ratZero q

def pfzGeneralIsZeroVector : pfzGeneralResidual -> Prop
  | [] => 0 = 0
  | x :: xs => RatEq x ratZero ∧ pfzGeneralIsZeroVector xs

def pfzGeneralResidualHasNonzeroCoordinate (v : pfzGeneralResidual) : Prop :=
  ∃ i : Fin v.length, pfzGeneralRatNonzero (v.get i)

def pfzGeneralResidualHasDetectedCoordinate (v : pfzGeneralResidual) : Prop :=
  ∃ i : Fin v.length, pfzGeneralRatCoordinateDetected (v.get i)

structure pfzGeneralSingletonEvent (v : pfzGeneralResidual) where
  index : Fin v.length
  coefficient_nonzero : pfzGeneralRatNonzero (v.get index)
  coefficient_detected : pfzGeneralRatCoordinateDetected (v.get index)

structure pfzGeneralResidueSingletonEvent
    (qs : List Nat) (p : Nat) (v : pfzGeneralResidual) where
  residue_address : Fin qs.length
  coefficient_address : Fin v.length
  residue_nonzero : pfzGeneralClassifierMod p (qs.get residue_address) ≠ 0
  coefficient_nonzero : pfzGeneralRatNonzero (v.get coefficient_address)
  coefficient_detected : pfzGeneralRatCoordinateDetected (v.get coefficient_address)

private def pfzGeneralUnaryHistoryDecidable : (h : BHist) -> Decidable (UnaryHistory h)
  | BHist.Empty => isTrue unary_empty
  | BHist.e0 _ => isFalse (fun h => h)
  | BHist.e1 h => pfzGeneralUnaryHistoryDecidable h

private instance (h : BHist) : Decidable (UnaryHistory h) :=
  pfzGeneralUnaryHistoryDecidable h

private instance (h k : BHist) : Decidable (hsame h k) := by
  unfold hsame
  infer_instance

private instance (x : BHist × BHist) :
    Decidable (BEDC.Derived.IntUp.IntPairCarrier x.1 x.2) := by
  unfold BEDC.Derived.IntUp.IntPairCarrier
  infer_instance

private instance (x y : BHist × BHist) :
    Decidable (BEDC.Derived.IntUp.IntPairClassifier x y) := by
  unfold BEDC.Derived.IntUp.IntPairClassifier
  infer_instance

private instance (x y : BEDC.Derived.PrimeUp.IntegerUp) :
    Decidable (BEDC.Derived.RationalUp.IntEq x y) := by
  unfold BEDC.Derived.RationalUp.IntEq
  infer_instance

private instance (x y : RatNum) : Decidable (RatEq x y) := by
  unfold RatEq
  infer_instance

theorem pfzGeneral_rat_coordinate_detected_of_nonzero (q : RatNum) :
    pfzGeneralRatNonzero q -> pfzGeneralRatCoordinateDetected q := by
  intro hneq
  cases ratLe_decidable q ratZero with
  | inl qLeZero =>
      cases ratLe_decidable ratZero q with
      | inl zeroLeQ =>
          exact False.elim (hneq (ratLe_antisymm qLeZero zeroLeQ))
      | inr notZeroLeQ =>
          exact Or.inl (ratLe_not_le_to_ratLt qLeZero notZeroLeQ)
  | inr notQLeZero =>
      have zeroLeQ : ratLe ratZero q :=
        Or.resolve_right (ratLe_total ratZero q) notQLeZero
      exact Or.inr (ratLe_not_le_to_ratLt zeroLeQ notQLeZero)

theorem pfzGeneral_residual_nonzero_coordinate :
    ∀ v : pfzGeneralResidual,
      (pfzGeneralIsZeroVector v -> False) ->
        pfzGeneralResidualHasNonzeroCoordinate v
  | [], h => by
      exact False.elim (h rfl)
  | x :: xs, h => by
      by_cases hx : RatEq x ratZero
      · have tailNotZero : pfzGeneralIsZeroVector xs -> False := by
          intro hxs
          exact h (And.intro hx hxs)
        obtain ⟨i, hi⟩ :=
          pfzGeneral_residual_nonzero_coordinate xs tailNotZero
        refine ⟨⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩, ?_⟩
        change pfzGeneralRatNonzero (xs.get i)
        exact hi
      · refine ⟨⟨0, Nat.succ_pos xs.length⟩, ?_⟩
        change pfzGeneralRatNonzero x
        exact hx

theorem pfzGeneral_residual_detected_coordinate :
    ∀ v : pfzGeneralResidual,
      (pfzGeneralIsZeroVector v -> False) ->
        pfzGeneralResidualHasDetectedCoordinate v := by
  intro v h
  obtain ⟨i, hi⟩ := pfzGeneral_residual_nonzero_coordinate v h
  exact ⟨i, pfzGeneral_rat_coordinate_detected_of_nonzero (v.get i) hi⟩

theorem pfzGeneral_nonzero_vector_detected_by_singleton_event
    (v : pfzGeneralResidual)
    (h : pfzGeneralIsZeroVector v -> False) :
    ∃ event : pfzGeneralSingletonEvent v,
      pfzGeneralRatNonzero (v.get event.index) ∧
        pfzGeneralRatCoordinateDetected (v.get event.index) := by
  obtain ⟨i, hi⟩ := pfzGeneral_residual_nonzero_coordinate v h
  let event : pfzGeneralSingletonEvent v :=
    { index := i
      coefficient_nonzero := hi
      coefficient_detected :=
        pfzGeneral_rat_coordinate_detected_of_nonzero (v.get i) hi }
  exact ⟨event, event.coefficient_nonzero, event.coefficient_detected⟩

theorem pfzGeneral_prime_modulus_detects_nonzero_vector_at_address
    {qs : List Nat} {p : Nat}
    (cert : pfzGeneralPrimeModulusCertificate qs p)
    (address : Fin qs.length)
    (v : pfzGeneralResidual)
    (h : pfzGeneralIsZeroVector v -> False) :
    ∃ event : pfzGeneralResidueSingletonEvent qs p v,
      event.residue_address = address := by
  have detected := pfzGeneral_prime_modulus_certificate_detects cert
  obtain ⟨i, hi⟩ := pfzGeneral_residual_nonzero_coordinate v h
  exact ⟨
    { residue_address := address
      coefficient_address := i
      residue_nonzero := detected.left address
      coefficient_nonzero := hi
      coefficient_detected :=
        pfzGeneral_rat_coordinate_detected_of_nonzero (v.get i) hi },
    rfl⟩

end BEDC.Derived.Visions
