import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel
import BEDC.GroundCompiler.MainTheorems

/-!
# TasteGate framework (hard schema, ground-compiler-derived)

`BHistCarrier X` forces a chapter to commit to a specific BHist embedding
of its tokens. `ChapterTasteGate X` then requires only the two genuinely
chapter-specific obligations:

* `round_trip`        — `fromEventFlow ∘ toEventFlow = some` on every token.
* `layer_separation`  — distinct tokens display as distinct event flows.

The other two TasteGate obligations (`conservativity` and
`no_hidden_input`) are *derived* — they fall out of `BHistCarrier` and the
ground-compiler `event_flow_conservativity` metalemma, so a chapter cannot
discharge them with `cases m` or a vacuous propositional placeholder.
The schema literally does not expose those obligations as fields; the
chapter can *only* supply data that genuinely involves its carrier.

This is the hard-enforcement version of the gate: ai-proposed chapters
that fail to define a real `BHistCarrier` (with a real `toEventFlow`
embedding and a real left-inverse `fromEventFlow`) cannot inhabit
`ChapterTasteGate` at all. The four obligations are then either
type-level inhabited (round_trip, layer_separation) or theorem-derived
from ground-compiler (conservativity, no_hidden_input).
-/

namespace BEDC.Meta.TasteGate

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.MainTheorems

/-- Embedding of a chapter carrier into the BEDC ground EventFlow.

A chapter must give a finite-history embedding of `X` into `EventFlow`
together with a partial inverse. The two are wired into a left-inverse
pair via `ChapterTasteGate.round_trip`. -/
class BHistCarrier (X : Type) where
  toEventFlow : X → EventFlow
  fromEventFlow : EventFlow → Option X

/-- The hard-enforcement taste gate. Chapter supplies only the two
chapter-specific obligations; conservativity and no-hidden-input are
*derived* outside the class via ground-compiler metalemmas. -/
class ChapterTasteGate (X : Type) [BHistCarrier X] where
  /-- Round trip: `fromEventFlow ∘ toEventFlow = some` on every token.
  Chapter must define `BHistCarrier.fromEventFlow` to actually invert the
  display; trivial `Unit` carriers fail this when fromEventFlow is
  constant. -/
  round_trip :
    ∀ (x : X),
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x

  /-- Layer separation: distinct tokens display as distinct event flows.
  Forces `BHistCarrier.toEventFlow` to be injective. Combinatorial
  padding chapters whose tokens share the same display can never
  inhabit this. -/
  layer_separation :
    ∀ (x y : X), x ≠ y →
      BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y

/-! ## Derived obligations

`conservativity` and `no_hidden_input` are not fields — they are
theorems automatically discharged by the ground compiler's
`event_flow_conservativity` and the `BHistCarrier` left-inverse pair.
Chapter cannot supply a vacuous version because the schema does not
let them. -/

/-- Conservativity is derived from `event_flow_conservativity`: for any
chapter `X`, every mark in any `toEventFlow x` event flow is one of the
two ground display marks. The chapter cannot bypass this — the proof
literally invokes the ground-compiler theorem. -/
theorem ChapterTasteGate.conservativity
    {X : Type} [BHistCarrier X] [ChapterTasteGate X] :
    ∀ (x : X) (w : RawEvent) (m : DisplayAlphabet),
      List.Mem w (BHistCarrier.toEventFlow x) →
      List.Mem m w →
      m = BMark.b0 ∨ m = BMark.b1 := by
  intro _ w m hw hm
  exact event_flow_conservativity (S := BHistCarrier.toEventFlow _) hw hm

/-- No-hidden-input is derived from `BHistCarrier.round_trip`: every
chapter token is the recognised image of its own display. The proof
forces a real `fromEventFlow` because the witness reads back through
it. -/
theorem ChapterTasteGate.no_hidden_input
    {X : Type} [BHistCarrier X] [ChapterTasteGate X] :
    ∀ (x : X), ∃ (e : EventFlow), BHistCarrier.fromEventFlow e = some x := by
  intro x
  exact ⟨BHistCarrier.toEventFlow x, ChapterTasteGate.round_trip x⟩

/-! ## Reference instance: the ground compiler chapter itself.

The ground compiler trivially satisfies the gate. Carrier is `EventFlow`
displayed as identity; `round_trip` is `rfl`; `layer_separation` follows
from `Option.some.inj` after `toEventFlow = id`. -/

instance groundCompilerBHistCarrier : BHistCarrier EventFlow where
  toEventFlow := id
  fromEventFlow := fun e => some e

instance groundCompilerChapterTasteGate : ChapterTasteGate EventFlow where
  round_trip := fun _ => rfl
  layer_separation := by
    intro x y hxy heq
    apply hxy
    exact heq

/-- Public alias preserved for backward compatibility with paper markers. -/
def groundCompilerSelfTasteGate : ChapterTasteGate EventFlow :=
  groundCompilerChapterTasteGate

end BEDC.Meta.TasteGate
