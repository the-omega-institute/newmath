import BEDC.Meta.TasteGate

/-!
# BeliefUp: minimal inductive carrier and TasteGate instance.

A `BeliefUp` token is a finite belief history with two constructors:

* `empty`   — the prior, no observations yet
* `observed` — a token recording that one observation has been folded in

This is the minimal nontrivial carrier required to exercise the schema
TasteGate: two distinct constructors prove the layer-separation
obligation isn't vacuous (`empty ≠ observed`), and the BHist embedding
maps `empty` to the empty event flow and `observed` to a one-event flow
of a single `b1` mark. The chapter remains at seedClosure on the paper
side; this Lean module commits to the carrier shape so that the
TasteGate instance is a real witness rather than a placeholder.
-/

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- A finite belief history. -/
inductive BeliefUp : Type where
  | empty : BeliefUp
  | observed : BeliefUp
  deriving DecidableEq

/-- Display embedding: empty prior is the empty flow; an observed token is a
single one-event flow carrying a `b1` mark. -/
def beliefToEventFlow : BeliefUp → EventFlow
  | BeliefUp.empty => []
  | BeliefUp.observed => [[BMark.b1]]

/-- Inverse readback. The chapter accepts only the two specific event flows
its display can emit; anything else is a hidden / unrecognised input. -/
def beliefFromEventFlow : EventFlow → Option BeliefUp
  | [] => some BeliefUp.empty
  | [[BMark.b1]] => some BeliefUp.observed
  | _ => none

instance beliefBHistCarrier : BHistCarrier BeliefUp where
  toEventFlow := beliefToEventFlow
  fromEventFlow := beliefFromEventFlow

instance beliefChapterTasteGate : ChapterTasteGate BeliefUp where
  conservativity := by
    intro x w m hw hm
    cases m with
    | b0 => exact Or.inl rfl
    | b1 => exact Or.inr rfl
  no_hidden_input := by
    intro x
    cases x with
    | empty => exact ⟨[], rfl⟩
    | observed => exact ⟨[[BMark.b1]], rfl⟩
  round_trip := by
    intro x
    cases x with
    | empty => rfl
    | observed => rfl
  layer_separation := by
    intro x y hxy heq
    cases x with
    | empty =>
      cases y with
      | empty => exact hxy rfl
      | observed => simp [BHistCarrier.toEventFlow, beliefToEventFlow] at heq
    | observed =>
      cases y with
      | empty => simp [BHistCarrier.toEventFlow, beliefToEventFlow] at heq
      | observed => exact hxy rfl

/-- Public alias matching the audit-gate marker
`BEDC.Derived.BeliefUp.taste_gate`. -/
def taste_gate : ChapterTasteGate BeliefUp := beliefChapterTasteGate

end BEDC.Derived.BeliefUp
