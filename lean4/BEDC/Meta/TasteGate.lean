import BEDC.FKernel.Hist
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

open BEDC.FKernel.Hist
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

/-! ## FieldFaithful: encoding reflects carrier-field structure.

`ChapterTasteGate.round_trip` + `layer_separation` together only force
`toEventFlow` to be injective on inhabitants. They do NOT force the
encoding to actually reflect the multi-field BHist structure of the
carrier — a chapter with `XUp.mk a b c d e f g h i` (9 BHist fields)
could conceivably encode only `(a, b)` and discard the remaining 7
fields, still pass round_trip + layer_separation under a constructed
`fromEventFlow` that reads them back from a hidden table.

`FieldFaithful` closes this loophole: the chapter must declare a
`fields : X → List BHist` projection that flattens every BHist
sub-field of the carrier (the canonical `.mk` projection list), and
prove `field_faithful`: two inhabitants with the same field list are
equal. Combined with `BHistCarrier.toEventFlow` being a function of
`fields` (chapters wire this via their own encode function), the
encoding inherits faithfulness of every field, not just the
projected ones.

This is intentionally OPT-IN (separate class from `ChapterTasteGate`)
so existing chapters compile unchanged. The Phase D paper-side gate
enforces it for `\origin{ai}` chapters; `\origin{human}` chapters
need not inhabit it (their nontriviality is attested by the external
mathematical record). -/

/-- Faithful field projection for a chapter carrier. The chapter must
    name its BHist sub-fields and prove that two inhabitants agree iff
    every field agrees. -/
class FieldFaithful (X : Type) [BHistCarrier X] where
  /-- Projection: list every BHist sub-field of a carrier inhabitant.
      For `XUp.mk a b c ... i`, this is `[a, b, c, ..., i]`. -/
  fields : X → List BHist

  /-- Faithfulness: same field list ⇒ same inhabitant.

      Combined with `BHistCarrier.toEventFlow` being a function of the
      `fields` projection (the standard chapter pattern), this forces
      the encoding to reflect every declared BHist sub-field. A chapter
      cannot declare 9 sub-fields but encode only 2 of them, because
      then `field_faithful` would witness two non-equal inhabitants
      with the same field list, which contradicts the requirement. -/
  field_faithful :
    ∀ (x y : X), fields x = fields y → x = y

/-! ## No reference FieldFaithful instance for `EventFlow`.

    Unlike `ChapterTasteGate`, where the ground compiler trivially
    inhabits via identity `toEventFlow`, `FieldFaithful` cannot be
    inhabited for `EventFlow` because the carrier's `BHist` sub-field
    list is genuinely empty (an `EventFlow` is a List of RawEvent,
    not of `BHist`), so any `fields` projection that returns `[]`
    forces `field_faithful` to assert `∀ x y : EventFlow, x = y` which
    is false. This is correct: `FieldFaithful` is a chapter-side gate
    for carriers built on top of `BHist`-shaped inductive `.mk`
    constructors. The ground compiler `EventFlow` is the substrate,
    not a chapter. Faithful chapters opt in by providing their own
    `.mk`-derived `fields` projection and proving `field_faithful`
    by case-analysis on `.mk`. -/

end BEDC.Meta.TasteGate
