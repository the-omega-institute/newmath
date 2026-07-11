import BEDC.Derived.Visions.PythagoreanRPCertificate

set_option maxHeartbeats 2000000

/-!
# Self-substitution carry holonomy witness

This file records a finite carry-holonomy no-go witness for the
self-substitution reflection-positivity branch.  The gain graph is the signed
one-state carry loop with gain `-1`; its cycle holonomy is therefore nontrivial.

Scope: this is a finite witness for the carry-holonomy mechanism and a pointer
to the existing Pythagorean `L = 3` negative quadratic-form certificate.  It is
not RH evidence and does not prove a general Hilbert--Polya obstruction.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

/-- A directed gain edge between finite carry/reflection states. -/
structure GainEdge where
  source : Nat
  target : Nat
  gain : RatNum

/-- Cycle holonomy is the ordered product of edge gains. -/
def cycleHolonomy : List GainEdge -> RatNum
  | [] => ratOne
  | edge :: rest => ratMul edge.gain (cycleHolonomy rest)

/-- A finite gain graph with an explicit list of cycles under inspection. -/
structure GainGraph where
  vertices : List Nat
  cycles : List (List GainEdge)

/-- Balanced means every inspected cycle has trivial holonomy. -/
def Balanced (G : GainGraph) : Prop :=
  ∀ cycle, cycle ∈ G.cycles -> RatEq (cycleHolonomy cycle) ratOne

/-- The minimal signed carry loop: one state and one edge of gain `-1`. -/
def signedCarryLoopEdge : GainEdge :=
  { source := 0, target := 0, gain := ratNeg ratOne }

/-- The signed one-edge carry cycle. -/
def signedCarryCycle : List GainEdge :=
  [signedCarryLoopEdge]

/-- The concrete finite gain graph used by this witness. -/
def signedCarryGraph : GainGraph :=
  { vertices := [0], cycles := [signedCarryCycle] }

theorem signed_carry_cycle_closed :
    signedCarryLoopEdge.source = 0 ∧ signedCarryLoopEdge.target = 0 := by
  constructor
  · rfl
  · rfl

theorem signed_carry_cycle_holonomy_eq_neg_one :
    RatEq (cycleHolonomy signedCarryCycle) (ratNeg ratOne) := by
  unfold signedCarryCycle signedCarryLoopEdge cycleHolonomy
  exact ratMul_one_right (ratNeg ratOne)

private theorem ratNegOne_lt_zero :
    ratLt (ratNeg ratOne) ratZero := by
  have raw :
      ratLt (ratSub ratZero ratOne) (ratSub ratZero ratZero) :=
    const_sub_strictAnti (a := ratZero) (b := ratOne) (c := ratZero)
      BEDC.Real.RatNumLogEnclosure.ratOne_pos
  have leftEq : RatEq (ratNeg ratOne) (ratSub ratZero ratOne) := by
    unfold ratSub
    exact RatEq_symm (ratZero_add_left (ratNeg ratOne))
  have rightEq : RatEq (ratSub ratZero ratZero) ratZero :=
    ratSub_self ratZero
  have shiftedLeft :
      ratLt (ratNeg ratOne) (ratSub ratZero ratZero) :=
    ratLt_of_RatEq_left leftEq raw
  exact ratLt_of_RatEq_right shiftedLeft rightEq

private theorem ratNegOne_lt_one :
    ratLt (ratNeg ratOne) ratOne :=
  ratLt_trans ratNegOne_lt_zero BEDC.Real.RatNumLogEnclosure.ratOne_pos

private theorem ratNegOne_not_ratOne :
    RatEq (ratNeg ratOne) ratOne -> False := by
  intro same
  exact ratLt_not_RatEq ratNegOne_lt_one same

theorem signed_carry_cycle_holonomy_not_one :
    RatEq (cycleHolonomy signedCarryCycle) ratOne -> False := by
  intro same
  exact ratNegOne_not_ratOne
    (RatEq_trans _ _ _
      (RatEq_symm signed_carry_cycle_holonomy_eq_neg_one)
      same)

theorem signed_carry_graph_not_balanced :
    Balanced signedCarryGraph -> False := by
  intro balanced
  have selected : signedCarryCycle ∈ signedCarryGraph.cycles := by
    unfold signedCarryGraph
    exact List.Mem.head _
  exact signed_carry_cycle_holonomy_not_one
    (balanced signedCarryCycle selected)

/--
Concrete bridge package: the same finite witness records nontrivial carry
holonomy and points to the already formalized Pythagorean `L = 3` negative
quadratic form.
-/
structure CarryHolonomyNegativeCertificate where
  cycle : List GainEdge
  holonomy_neutral_absurd : RatEq (cycleHolonomy cycle) ratOne -> False
  rpQuadraticForm : RatNum
  rpQuadraticForm_negative : ratLt rpQuadraticForm ratZero

/-- The signed carry holonomy witness paired with the Pythagorean RP failure certificate. -/
def signedCarryHolonomyNegativeCertificate :
    CarryHolonomyNegativeCertificate :=
  { cycle := signedCarryCycle
    holonomy_neutral_absurd := signed_carry_cycle_holonomy_not_one
    rpQuadraticForm := pythagoreanLThreeQuadraticForm
    rpQuadraticForm_negative :=
      pythagorean_lthree_negative_quadratic_form.right }

theorem signed_carry_holonomy_refs_pythagorean_negative_form :
    (RatEq (cycleHolonomy signedCarryCycle) ratOne -> False) ∧
      ratLt pythagoreanLThreeQuadraticForm ratZero := by
  constructor
  · exact signed_carry_cycle_holonomy_not_one
  · exact pythagorean_lthree_negative_quadratic_form.right

end BEDC.Derived.Visions
