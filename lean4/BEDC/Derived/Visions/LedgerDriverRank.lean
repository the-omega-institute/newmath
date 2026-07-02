import BEDC.Derived.Visions.TwoDriverMetricNondegeneracy
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 400000

/-!
# Ledger driver rank bridge

This file gives the schematic bridge between append-only observation ledgers and the
two-driver backreaction determinant.  A raw observation ledger is represented as a
`List DriverVec`; its adjacent differences are the candidate drivers.  The bridge is
deliberately algebraic: it proves that collinear drivers force every two-driver
determinant to vanish, and that a nonzero determinant therefore needs a noncollinear
pair.  It does not assert that an observation ledger actually supplies independent
drivers; that remains an open empirical/modeling question.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Derived.IntUp

/-- A schematic two-component driver vector. -/
abbrev DriverVec := RatNum × RatNum

/-- Difference of two schematic 2-vectors. -/
def driverDelta (next prev : DriverVec) : DriverVec :=
  (ratSub next.1 prev.1, ratSub next.2 prev.2)

/-- Adjacent differences extracted from a raw observation ledger. -/
def ledgerAdjacentDrivers : List DriverVec -> List DriverVec
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      driverDelta second first :: ledgerAdjacentDrivers (second :: rest)

/-- Ledger drivers, when the ledger is already expressed as a step sequence. -/
def ledgerDrivers (steps : List DriverVec) : List DriverVec :=
  steps

/-- The 2D wedge product of two schematic drivers. -/
def driverWedge (d1 d2 : DriverVec) : RatNum :=
  ratSub (ratMul d1.1 d2.2) (ratMul d1.2 d2.1)

/-- All drivers in a finite list are pairwise collinear. -/
def allCollinear (ds : List DriverVec) : Prop :=
  ∀ d1 d2 : DriverVec, List.Mem d1 ds -> List.Mem d2 ds -> RatEq (driverWedge d1 d2) ratZero

/-- The local wedge agrees with the two-driver wedge used by the metric determinant file. -/
theorem driverWedge_eq_wedge (d1 d2 : DriverVec) :
    RatEq (driverWedge d1 d2) (wedge d1.1 d1.2 d2.1 d2.2) :=
  RatEq_refl _

/-- A driver has zero wedge with itself. -/
private theorem driverWedge_self_zero (d : DriverVec) :
    RatEq (driverWedge d d) ratZero := by
  unfold driverWedge
  exact (ratSub_zero_iff (ratMul d.1 d.2) (ratMul d.2 d.1)).mpr (ratMul_comm d.1 d.2)

private theorem mem_singleton_driver_eq {head d : DriverVec} :
    List.Mem d [head] -> d = head := by
  intro h
  cases h with
  | head => rfl
  | tail _ htail => cases htail

private theorem singleton_driver_collinear (head : DriverVec) :
    allCollinear [head] := by
  intro d1 d2 h1 h2
  have e1 : d1 = head := mem_singleton_driver_eq h1
  have e2 : d2 = head := mem_singleton_driver_eq h2
  cases e1
  cases e2
  exact driverWedge_self_zero head

private theorem at_least_two_drivers_not_singleton
    (head second : DriverVec) (rest : List DriverVec) :
    Not ((head :: second :: rest).length ≤ 1) := by
  intro hlen
  change Nat.succ (Nat.succ rest.length) ≤ Nat.succ Nat.zero at hlen
  exact Nat.not_succ_le_zero rest.length (Nat.le_of_succ_le_succ hlen)

/-- A rational with zero numerator is equal to `0` under `RatEq`. -/
private theorem ratNum_zero_to_RatEq_zero_local {x : RatNum} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

/-- Multiplication by zero on the right, exposed locally as `RatEq`. -/
private theorem ratMul_zero_right_local (x : RatNum) :
    RatEq (ratMul x ratZero) ratZero := by
  apply ratNum_zero_to_RatEq_zero_local
  unfold ratMul ratZero intToRat
  change IntEq (IntMul x.num intZero) intZero
  exact intMul_zero_right x.num

/-- If the wedge is zero, the explicit weighted wedge-square determinant term is zero. -/
private theorem weighted_wedge_sq_zero
    (w1 w2 a1 a2 b1 b2 : RatNum)
    (hw : RatEq (wedge a1 a2 b1 b2) ratZero) :
    RatEq
      (ratMul (ratMul (ratMul w1 w2) (wedge a1 a2 b1 b2)) (wedge a1 a2 b1 b2))
      ratZero := by
  refine RatEq_trans _ (ratMul (ratMul (ratMul w1 w2) (wedge a1 a2 b1 b2)) ratZero) _ ?_ ?_
  · exact ratMul_respects_right hw
  · exact ratMul_zero_right_local (ratMul (ratMul w1 w2) (wedge a1 a2 b1 b2))

/-- A driver list of length at most one is vacuously collinear. -/
theorem single_step_ledger_collinear (ds : List DriverVec) :
    ds.length ≤ 1 -> allCollinear (ledgerDrivers ds) := by
  intro hlen
  unfold ledgerDrivers
  cases ds with
  | nil =>
      unfold allCollinear
      intro d1 d2 h1 _h2
      cases h1
  | cons head tail =>
      cases tail with
      | nil =>
          exact singleton_driver_collinear head
      | cons second rest =>
          exact False.elim (at_least_two_drivers_not_singleton head second rest hlen)

/-- Collinearity forces every two-driver metric determinant selected from the list to vanish. -/
theorem collinear_implies_degenerate
    (ds : List DriverVec) (hcol : allCollinear ds)
    (w1 w2 : RatNum) {d1 d2 : DriverVec}
    (hd1 : List.Mem d1 ds) (hd2 : List.Mem d2 ds) :
    RatEq (twoDriverMetricDet w1 w2 d1.1 d1.2 d2.1 d2.2) ratZero := by
  have hwDriver : RatEq (driverWedge d1 d2) ratZero := hcol d1 d2 hd1 hd2
  have hw : RatEq (wedge d1.1 d1.2 d2.1 d2.2) ratZero :=
    RatEq_trans _ _ _ (RatEq_symm (driverWedge_eq_wedge d1 d2)) hwDriver
  exact RatEq_trans _ _ _
    (two_driver_det_eq_weighted_wedge_sq w1 w2 d1.1 d1.2 d2.1 d2.2)
    (weighted_wedge_sq_zero w1 w2 d1.1 d1.2 d2.1 d2.2 hw)

/-- A nonzero two-driver determinant rules out collinearity of that driver pair. -/
theorem nondegenerate_needs_noncollinear
    (w1 w2 : RatNum) (d1 d2 : DriverVec)
    (hdet : Not (RatEq (twoDriverMetricDet w1 w2 d1.1 d1.2 d2.1 d2.2) ratZero)) :
    Not (RatEq (driverWedge d1 d2) ratZero) := by
  intro hcol
  have hw : RatEq (wedge d1.1 d1.2 d2.1 d2.2) ratZero :=
    RatEq_trans _ _ _ (RatEq_symm (driverWedge_eq_wedge d1 d2)) hcol
  exact hdet (RatEq_trans _ _ _
    (two_driver_det_eq_weighted_wedge_sq w1 w2 d1.1 d1.2 d2.1 d2.2)
    (weighted_wedge_sq_zero w1 w2 d1.1 d1.2 d2.1 d2.2 hw))

end BEDC.Derived.Visions
