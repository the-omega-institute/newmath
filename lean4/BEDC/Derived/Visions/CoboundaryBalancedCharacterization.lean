import BEDC.Derived.Visions.SaturatedCycleLemma
import BEDC.Derived.Visions.SelfSubstitutionCarryHolonomy

set_option maxHeartbeats 2000000

/-!
# Coboundary-balanced characterization for the self-substitution RP no-go route

This file formalizes the signed, finite gain-graph core of the capstone:
coboundary gains telescope to trivial closed-walk holonomy, hence a graph with
a witnessed nontrivial cycle is not a coboundary.  The homological
identification between observable and raw cycle lattices is left as an
explicit statement-level structure field in the surrounding program, not as a
claim proved here.

Scope: this is a constructive no-go component for the Hilbert--Polya via
self-substitution construction class.  It is not evidence for RH.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

/-- Signed potentials use only the two rational units `+1` and `-1`. -/
def SignedUnit (x : RatNum) : Prop :=
  RatEq x ratOne ∨ RatEq x (ratNeg ratOne)

/-- The signed inverse is the element itself, for the two-element unit group. -/
def signedInv (x : RatNum) : RatNum :=
  x

/-- A signed potential assigns a rational sign to every vertex. -/
structure SignedPotential where
  value : Nat -> RatNum
  signed : ∀ v : Nat, SignedUnit (value v)

/-- The coboundary gain on an edge is `g(target) * g(source)^{-1}`. -/
def coboundaryGain (g : SignedPotential) (e : GainEdge) : RatNum :=
  ratMul (g.value e.target) (signedInv (g.value e.source))

/-- A gain graph is a signed coboundary when all inspected edge gains come from one potential. -/
def IsCoboundary (G : GainGraph) : Prop :=
  ∃ g : SignedPotential,
    ∀ cycle, cycle ∈ G.cycles ->
      ∀ edge, edge ∈ cycle -> RatEq edge.gain (coboundaryGain g edge)

/-- `PathFromTo s t walk` records composable endpoints for the displayed walk. -/
def PathFromTo (s t : Nat) : List GainEdge -> Prop
  | [] => s = t
  | edge :: rest => edge.source = s ∧ PathFromTo edge.target t rest

/-- Closed walks are paths whose source and target coincide. -/
def ClosedWalk (cycle : List GainEdge) : Prop :=
  ∃ v : Nat, PathFromTo v v cycle

/-- The cycles declared in the graph are exactly the closed walks inspected by `Balanced`. -/
def CyclesClosed (G : GainGraph) : Prop :=
  ∀ cycle, cycle ∈ G.cycles -> ClosedWalk cycle

private theorem ratEq_trans_local {x y z : RatNum} :
    RatEq x y -> RatEq y z -> RatEq x z :=
  RatEq_trans x y z

private theorem signed_unit_square_one {x : RatNum} :
    SignedUnit x -> RatEq (ratMul x x) ratOne := by
  intro hx
  cases hx with
  | inl hOne =>
      exact ratEq_trans_local
        (ratMul_respects hOne hOne)
        (ratOne_mul_left ratOne)
  | inr hNeg =>
      have mulNeg :
          RatEq (ratMul (ratNeg ratOne) (ratNeg ratOne)) ratOne := by
        apply ratEq_of_num_den_intEq
        · unfold ratMul ratNeg ratOne intToRat intOne intOfNat
          change IntEq
            (IntMul
              (BEDC.Derived.RationalUp.intNeg
                (BEDC.Derived.RationalUp.intNeg intOne))
              intOne)
            intOne
          exact IntEq_trans
            (intMul_one_right
              (BEDC.Derived.RationalUp.intNeg
                (BEDC.Derived.RationalUp.intNeg intOne)))
            (BEDC.Algebra.Rel.IntegerUp_neg_neg intOne)
        · unfold ratMul ratNeg ratOne intToRat ratDenInt intOne intOfNat
          exact IntEq_refl _
      exact ratEq_trans_local (ratMul_respects hNeg hNeg) mulNeg

private theorem signed_unit_cancel_middle {x y z : RatNum} :
    SignedUnit y ->
      RatEq (ratMul (ratMul x y) (ratMul y z)) (ratMul x z) := by
  intro hy
  have regroup :
      RatEq (ratMul (ratMul x y) (ratMul y z))
        (ratMul x (ratMul (ratMul y y) z)) := by
    exact ratEq_trans_local
      (ratMul_assoc x y (ratMul y z))
      (ratMul_respects (RatEq_refl x)
        (RatEq_symm (ratMul_assoc y y z)))
  have squareOne : RatEq (ratMul y y) ratOne :=
    signed_unit_square_one hy
  have dropSquare :
      RatEq (ratMul x (ratMul (ratMul y y) z)) (ratMul x z) := by
    exact ratMul_respects (RatEq_refl x)
      (ratEq_trans_local
        (ratMul_respects squareOne (RatEq_refl z))
        (ratOne_mul_left z))
  exact ratEq_trans_local regroup dropSquare

private theorem signed_unit_cancel_bridge {a b c : RatNum} :
    SignedUnit b ->
      RatEq (ratMul (ratMul b a) (ratMul c b)) (ratMul c a) := by
  intro hb
  exact ratEq_trans_local
    (ratMul_comm (ratMul b a) (ratMul c b))
    (signed_unit_cancel_middle (x := c) (y := b) (z := a) hb)

private theorem cycleHolonomy_respects_edge_gains
    {cycle : List GainEdge} {g : GainEdge -> RatNum}
    (h : ∀ edge, edge ∈ cycle -> RatEq edge.gain (g edge)) :
    RatEq (cycleHolonomy cycle)
      (cycle.foldr (fun edge acc => ratMul (g edge) acc) ratOne) := by
  induction cycle with
  | nil =>
      exact RatEq_refl ratOne
  | cons edge rest ih =>
      unfold cycleHolonomy List.foldr
      exact ratMul_respects
        (h edge (List.Mem.head rest))
        (ih (fun e mem => h e (List.Mem.tail edge mem)))

private theorem coboundary_path_holonomy_aux
    (g : SignedPotential) {s t : Nat} {walk : List GainEdge}
    (path : PathFromTo s t walk) :
    RatEq
      (walk.foldr (fun edge acc => ratMul (coboundaryGain g edge) acc) ratOne)
      (ratMul (g.value t) (g.value s)) := by
  induction walk generalizing s with
  | nil =>
      cases path
      exact RatEq_symm (signed_unit_square_one (g.signed t))
  | cons edge rest ih =>
      have sourceEq : edge.source = s := path.left
      have restPath : PathFromTo edge.target t rest := path.right
      cases sourceEq
      unfold List.foldr coboundaryGain signedInv
      have tailEq :
          RatEq
            (rest.foldr (fun edge acc => ratMul (coboundaryGain g edge) acc) ratOne)
            (ratMul (g.value t) (g.value edge.target)) :=
        ih restPath
      exact ratEq_trans_local
        (ratMul_respects
          (RatEq_refl (ratMul (g.value edge.target) (g.value edge.source)))
          tailEq)
        (signed_unit_cancel_bridge (a := g.value edge.source)
          (b := g.value edge.target) (c := g.value t) (g.signed edge.target))

/-- A potential-generated signed gain telescopes to neutral holonomy on every closed walk. -/
theorem coboundary_closed_cycle_holonomy_one
    (g : SignedPotential) {cycle : List GainEdge}
    (path : ClosedWalk cycle)
    (edgeGain :
      ∀ edge, edge ∈ cycle -> RatEq edge.gain (coboundaryGain g edge)) :
    RatEq (cycleHolonomy cycle) ratOne := by
  cases path with
  | intro v closedPath =>
      exact ratEq_trans_local
        (cycleHolonomy_respects_edge_gains edgeGain)
        (ratEq_trans_local
          (coboundary_path_holonomy_aux g closedPath)
          (signed_unit_square_one (g.signed v)))

/--
Coboundary gain data are balanced on every inspected closed cycle.  This is
the constructive direction of the finite signed characterization.
-/
theorem coboundary_implies_balanced
    {G : GainGraph} :
    CyclesClosed G -> IsCoboundary G -> Balanced G := by
  intro closed coboundary cycle cycleMem
  cases coboundary with
  | intro g generated =>
      exact coboundary_closed_cycle_holonomy_one g
        (closed cycle cycleMem)
        (generated cycle cycleMem)

/-- Nontrivial holonomy on an inspected closed cycle forbids a coboundary potential. -/
theorem not_balanced_implies_not_coboundary
    {G : GainGraph} :
    CyclesClosed G ->
      (∃ cycle, cycle ∈ G.cycles ∧ (RatEq (cycleHolonomy cycle) ratOne -> False)) ->
        IsCoboundary G -> False := by
  intro closed witness coboundary
  cases witness with
  | intro cycle hw =>
      exact hw.right ((coboundary_implies_balanced closed coboundary) cycle hw.left)

theorem signed_carry_cycle_closed_walk :
    ClosedWalk signedCarryCycle := by
  exact ⟨0, by
    unfold signedCarryCycle signedCarryLoopEdge PathFromTo
    exact ⟨rfl, rfl⟩⟩

theorem signed_carry_graph_cycles_closed :
    CyclesClosed signedCarryGraph := by
  intro cycle hmem
  unfold signedCarryGraph at hmem
  cases hmem with
  | head _ =>
      exact signed_carry_cycle_closed_walk
  | tail _ tailMem =>
      cases tailMem

/-- The signed carry graph has a concrete unbalanced cycle, so it is not a coboundary. -/
theorem signed_carry_graph_not_coboundary :
    IsCoboundary signedCarryGraph -> False := by
  exact not_balanced_implies_not_coboundary
    signed_carry_graph_cycles_closed
    ⟨signedCarryCycle, by
      unfold signedCarryGraph
      exact List.Mem.head _,
      signed_carry_cycle_holonomy_not_one⟩

/--
Statement-level connector for the full-window RP predicate.  The saturated
cycle file provides the concrete non-PSD witness; the observable/raw cycle
lattice identification is an external homological connector, not proved here.
-/
structure AllWindowRP (G : GainGraph) where
  everyInspectedCycleClosed : CyclesClosed G
  observableRawCycleLatticeIdentified : Prop

theorem signed_carry_capstone_no_go :
    (Balanced signedCarryGraph -> False) ∧
      (IsCoboundary signedCarryGraph -> False) ∧
        (∃ w : List RatNum, ∃ q : RatNum,
          w = satCycleWitness ∧
            SaturatedCycleNegativeDirection cycleGramMinusOne w q) := by
  constructor
  · exact signed_carry_graph_not_balanced
  · constructor
    · exact signed_carry_graph_not_coboundary
    · exact saturated_cycle_gram_not_psd

end BEDC.Derived.Visions
