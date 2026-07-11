import BEDC.Derived.RationalUp

namespace BEDC.Derived.RHRoute.CopenhagenNoScale

open BEDC.Derived.RationalUp

/-
CopenhagenTowerData bundles the abstract no-scale skeleton proved in this
file with the RH-level capture input `energy_bounded`: every off-critical
zero is postulated, at the route boundary, to carry a bounded-energy
divergent solenoid-compatible tower. Constructing such data for an actual
zeta zero is RH-equivalent and is not provided here. This module proves only
the abstract implication, in the same conditional style as the
AnalyticGombocForXi route audit.
-/

abbrev BRat : Type :=
  RatNum

def Unbounded (W : Nat -> BRat) : Prop :=
  forall B : BRat, exists n, ratLt B (W n)

private theorem ratLt_respects_local {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratMul_left_cancel_inv_local
    (a b : BRat) (ha : ratApart0 a) :
    RatEq (ratMul a (ratMul b (ratInvApart a ha))) b := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc a b (ratInvApart a ha)))
    (RatEq_trans _ _ _
      (ratMul_respects_left (ratMul_comm a b))
      (RatEq_trans _ _ _
        (ratMul_assoc b a (ratInvApart a ha))
        (RatEq_trans _ _ _
          (ratMul_respects_right (ratInvApart_mul a ha))
          (ratMul_one_right b))))

theorem boundedEnergy_apart_absurd
    (r : BRat) (W : Nat -> BRat) (Bnd : BRat)
    (hWpos : forall n, ratLe ratZero (W n))
    (hWunb : Unbounded W)
    (hrsq_pos : ratLt ratZero (ratMul r r))
    (hbound :
      forall n, ratLe (ratMul (ratMul r r) (W n)) Bnd) :
    False := by
  let rsq := ratMul r r
  let rsqApart : ratApart0 rsq := ratPositive_num_nonzero hrsq_pos
  let threshold := ratMul Bnd (ratInvApart rsq rsqApart)
  cases hWunb threshold with
  | intro n hlarge =>
      have _ : ratLe ratZero (W n) := hWpos n
      have scaledLarge :
          ratLt (ratMul rsq threshold) (ratMul rsq (W n)) :=
        ratMul_lt_mul_left hlarge hrsq_pos
      have thresholdCancels :
          RatEq (ratMul rsq threshold) Bnd := by
        unfold threshold
        exact ratMul_left_cancel_inv_local rsq Bnd rsqApart
      have BndLtEnergy :
          ratLt Bnd (ratMul (ratMul r r) (W n)) := by
        unfold rsq at scaledLarge
        exact ratLt_respects_local thresholdCancels
          (RatEq_refl (ratMul (ratMul r r) (W n))) scaledLarge
      exact ratLt_not_ratLe_reverse BndLtEnergy (hbound n)

theorem boundedEnergy_forces_not_apart
    (r : BRat) (W : Nat -> BRat) (Bnd : BRat)
    (hWpos : forall n, ratLe ratZero (W n))
    (hWunb : Unbounded W)
    (hbound :
      forall n, ratLe (ratMul (ratMul r r) (W n)) Bnd) :
    (ratLt ratZero (ratMul r r) -> False) := by
  intro hrsq_pos
  exact boundedEnergy_apart_absurd r W Bnd hWpos hWunb hrsq_pos hbound

inductive CopenhagenCaptureObligation where
  | activeCapture
  | solenoidCompatibleBoundedEnergy
  | primeRoutingDefectInvariant

def canonicalCopenhagenCaptureObligations :
    List CopenhagenCaptureObligation :=
  [ CopenhagenCaptureObligation.activeCapture,
    CopenhagenCaptureObligation.solenoidCompatibleBoundedEnergy,
    CopenhagenCaptureObligation.primeRoutingDefectInvariant ]

theorem copenhagen_capture_obligation_count :
    canonicalCopenhagenCaptureObligations.length = 3 := by
  rfl

structure CopenhagenTowerData (r : BRat) where
  W : Nat -> BRat
  W_nonneg : forall n, ratLe ratZero (W n)
  W_unbounded : Unbounded W
  energy_bounded :
    exists Bnd, forall n, ratLe (ratMul (ratMul r r) (W n)) Bnd

/-
This theorem is a conditional no-scale audit statement. The proof consumes
the tower fields only after an external inhabitant of `CopenhagenTowerData`
has been supplied; this file gives no construction for zeta zeros and makes
no RH claim beyond the displayed implication.
-/
theorem copenhagenTower_forces_not_apart
    (r : BRat) (T : CopenhagenTowerData r) :
    (ratLt ratZero (ratMul r r) -> False) := by
  intro hrsq_pos
  cases T.energy_bounded with
  | intro Bnd hbound =>
      exact boundedEnergy_apart_absurd r T.W Bnd
        T.W_nonneg T.W_unbounded hrsq_pos hbound

end BEDC.Derived.RHRoute.CopenhagenNoScale
