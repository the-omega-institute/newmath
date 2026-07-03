import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Finite prime-classifier detection core

This file records only the unconditional finite part of the RH-route
scaffold: a concrete maximal-prime residue classifier separates the finite
sample `[2, 3, 5, 7]`, and a finite RatNum residual that is not zero has a
coordinate witness.  It does not assert that an off-line zero creates such a
residual, and it does not imply RH.
-/

namespace BEDC.Derived.Visions

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel

def primeClassifierMod (P x : Nat) : Nat :=
  x % P

def pfzPrimeClassifierModulus : Nat :=
  7

def pfzPrimeClassifierFinitePoints : List Nat :=
  [2, 3, 5, pfzPrimeClassifierModulus]

def pfzPrimeClassifierFiniteValues : List Nat :=
  pfzPrimeClassifierFinitePoints.map
    (primeClassifierMod pfzPrimeClassifierModulus)

theorem pfz_primeClassifier_sample_values :
    pfzPrimeClassifierFiniteValues = [2, 3, 5, 0] := by
  rfl

theorem pfz_primeClassifier_sample_values_distinct :
    pfzPrimeClassifierFiniteValues = [2, 3, 5, 0] ∧
      List.Nodup pfzPrimeClassifierFiniteValues := by
  constructor
  · exact pfz_primeClassifier_sample_values
  · decide

abbrev pfzResidual : Type :=
  List RatNum

def pfzRatNonzero (q : RatNum) : Prop :=
  RatEq q ratZero -> False

def pfzRatCoordinateDetected (q : RatNum) : Prop :=
  ratLt q ratZero ∨ ratLt ratZero q

def pfzIsZeroVector : pfzResidual -> Prop
  | [] => 0 = 0
  | x :: xs => RatEq x ratZero ∧ pfzIsZeroVector xs

def pfzResidualHasNonzeroCoordinate (v : pfzResidual) : Prop :=
  ∃ i : Fin v.length, pfzRatNonzero (v.get i)

def pfzResidualHasDetectedCoordinate (v : pfzResidual) : Prop :=
  ∃ i : Fin v.length, pfzRatCoordinateDetected (v.get i)

private def pfzUnaryHistoryDecidable : (h : BHist) -> Decidable (UnaryHistory h)
  | BHist.Empty => isTrue unary_empty
  | BHist.e0 _ => isFalse (fun h => h)
  | BHist.e1 h => pfzUnaryHistoryDecidable h

private instance (h : BHist) : Decidable (UnaryHistory h) :=
  pfzUnaryHistoryDecidable h

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

theorem pfz_rat_coordinate_detected_of_nonzero (q : RatNum) :
    pfzRatNonzero q -> pfzRatCoordinateDetected q := by
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

theorem pfz_residual_nonzero_coordinate :
    ∀ v : pfzResidual,
      (pfzIsZeroVector v -> False) ->
        pfzResidualHasNonzeroCoordinate v
  | [], h => by
      exact False.elim (h rfl)
  | x :: xs, h => by
      by_cases hx : RatEq x ratZero
      · have tailNotZero : pfzIsZeroVector xs -> False := by
          intro hxs
          exact h (And.intro hx hxs)
        obtain ⟨i, hi⟩ :=
          pfz_residual_nonzero_coordinate xs tailNotZero
        refine ⟨⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩, ?_⟩
        change pfzRatNonzero (xs.get i)
        exact hi
      · refine ⟨⟨0, Nat.succ_pos xs.length⟩, ?_⟩
        change pfzRatNonzero x
        exact hx

theorem pfz_residual_detected_coordinate :
    ∀ v : pfzResidual,
      (pfzIsZeroVector v -> False) ->
        pfzResidualHasDetectedCoordinate v := by
  intro v h
  obtain ⟨i, hi⟩ := pfz_residual_nonzero_coordinate v h
  exact ⟨i, pfz_rat_coordinate_detected_of_nonzero (v.get i) hi⟩

end BEDC.Derived.Visions
