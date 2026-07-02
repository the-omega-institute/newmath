import BEDC.Derived.RHRoute.CopenhagenNoScale
import BEDC.Derived.RHRoute.NormalDefectLedger
import BEDC.Real.RatNumLogEnclosure

namespace BEDC.Derived.RHRoute.ZetaOrientedTriadicTowerSkeleton

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

/-
This file records only the conditional skeleton: if a zeta-oriented tower is
externally supplied with all six named certificates, then the normal parameter
cannot have positive square. The full assertion that every zeta zero carries
such a tower is RH-equivalent; this module does not construct any certificate
and does not claim RH.
-/

-- Capture: the zero is caught by the canonical packet.
inductive ActiveCapture : Prop

-- Solenoid: scale variation enters only the compact phase fibre.
inductive SolenoidCompatibility : Prop

-- Triadic: the three axis routes close on the same tower object.
inductive TriadicClosure : Prop

-- Defect: the normal defect ledger extracts `E n = r^2 * W n`.
def DefectExtraction (r : Rat) (W E : Nat -> Rat) : Prop :=
  forall n, RatEq (E n) (ratMul (ratMul r r) (W n))

-- Cofinal: the weight sequence is unbounded along the tower.
def CofinalGrowth (W : Nat -> Rat) : Prop :=
  BEDC.Derived.RHRoute.CopenhagenNoScale.Unbounded W

-- Boundary: the defect energy is uniformly bounded; this is the RH-equivalent wall.
def BoundaryStability (E : Nat -> Rat) (Bnd : Rat) : Prop :=
  forall n, ratLe (E n) Bnd

def LedgerWeight (H : Nat -> List Rat) : Nat -> Rat :=
  fun n => BEDC.Derived.RHRoute.NormalDefectLedger.heightEnergy (H n)

def LedgerEnergy (r : Rat) (H : Nat -> List Rat) : Nat -> Rat :=
  fun n => BEDC.Derived.RHRoute.NormalDefectLedger.ledgerE r (H n)

def LedgerDefectExtractionInterface
    (r : Rat) (H : Nat -> List Rat) : Prop :=
  DefectExtraction r (LedgerWeight H) (LedgerEnergy r H)

structure TriadicTowerData where
  W : Nat -> Rat
  E : Nat -> Rat
  r : Rat
  Bnd : Rat
  W_nonneg : forall n, ratLe ratZero (W n)
  active_capture : ActiveCapture
  solenoid_compatibility : SolenoidCompatibility
  triadic_closure : TriadicClosure
  defect_extraction : DefectExtraction r W E
  cofinal_growth : CofinalGrowth W
  boundary_stability : BoundaryStability E Bnd

theorem triadicTower_forces_not_apart
    (T : TriadicTowerData) :
    (ratLt ratZero (ratMul T.r T.r) -> False) := by
  intro hrsq_pos
  apply BEDC.Derived.RHRoute.CopenhagenNoScale.boundedEnergy_apart_absurd
    T.r T.W T.Bnd T.W_nonneg T.cofinal_growth hrsq_pos
  intro n
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (RatEq_symm (T.defect_extraction n))
    (T.boundary_stability n)

theorem triadicTower_refutes_positive_scale :
    forall T : TriadicTowerData,
      ratLt ratZero (ratMul T.r T.r) -> False :=
  triadicTower_forces_not_apart

private theorem ratOne_square_positive :
    ratLt ratZero (ratMul ratOne ratOne) := by
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    BEDC.Real.RatNumLogEnclosure.ratOne_pos
    (RatEq_symm (ratOne_mul_left ratOne))

theorem unitScale_three_conditions_absurd
    (W E : Nat -> Rat) (Bnd : Rat)
    (hWnonneg : forall n, ratLe ratZero (W n))
    (hExtract : DefectExtraction ratOne W E)
    (hCofinal : CofinalGrowth W)
    (hBoundary : BoundaryStability E Bnd) :
    False := by
  apply BEDC.Derived.RHRoute.CopenhagenNoScale.boundedEnergy_apart_absurd
    ratOne W Bnd hWnonneg hCofinal ratOne_square_positive
  intro n
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (RatEq_symm (hExtract n))
    (hBoundary n)

theorem triadicTower_no_unit_scale
    (T : TriadicTowerData) (hr : RatEq T.r ratOne) :
    False := by
  apply triadicTower_forces_not_apart T
  have squareOne :
      RatEq (ratMul T.r T.r) ratOne := by
    exact RatEq_trans _ _ _
      (ratMul_respects hr hr)
      (ratOne_mul_left ratOne)
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    BEDC.Real.RatNumLogEnclosure.ratOne_pos
    (RatEq_symm squareOne)

end BEDC.Derived.RHRoute.ZetaOrientedTriadicTowerSkeleton
