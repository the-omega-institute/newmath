import BEDC.Meta.TasteGate

/-!
# BeliefUp: minimal inductive carrier and TasteGate instance (hard schema).

A `BeliefUp` token is a finite belief history with two constructors
(`empty` / `observed`). Under the hard schema, the chapter supplies only
`round_trip` and `layer_separation`; `conservativity` and `no_hidden_input`
are derived theorems that automatically invoke
`event_flow_conservativity` and the chapter's own `round_trip`.

This is the minimal nontrivial carrier required to pass the hard gate:
two distinct constructors prove `layer_separation` is non-vacuous, and
the BHist embedding is genuinely a left-inverse pair (empty ↔ empty
flow; observed ↔ one-event b1 flow).
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

/-- Display embedding: empty prior is the empty flow; an observed token is
a single one-event flow carrying a `b1` mark. -/
def beliefToEventFlow : BeliefUp → EventFlow
  | BeliefUp.empty => []
  | BeliefUp.observed => [[BMark.b1]]

/-- Inverse readback. The chapter accepts only the two specific event flows
its display can emit. -/
def beliefFromEventFlow : EventFlow → Option BeliefUp
  | [] => some BeliefUp.empty
  | [[BMark.b1]] => some BeliefUp.observed
  | _ => none

instance beliefBHistCarrier : BHistCarrier BeliefUp where
  toEventFlow := beliefToEventFlow
  fromEventFlow := beliefFromEventFlow

instance beliefChapterTasteGate : ChapterTasteGate BeliefUp where
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

theorem BeliefTasteGate_carrier_recognition :
    BHistCarrier.toEventFlow BeliefUp.empty = [] ∧
      BHistCarrier.toEventFlow BeliefUp.observed = [[BMark.b1]] ∧
        beliefFromEventFlow [] = some BeliefUp.empty ∧
          beliefFromEventFlow [[BMark.b1]] = some BeliefUp.observed ∧
            (forall x : BeliefUp, beliefFromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x
          cases x with
          | empty => rfl
          | observed => rfl

/-- Public alias matching the audit-gate marker
`BEDC.Derived.BeliefUp.taste_gate`. -/
def taste_gate : ChapterTasteGate BeliefUp := beliefChapterTasteGate

end BEDC.Derived.BeliefUp
