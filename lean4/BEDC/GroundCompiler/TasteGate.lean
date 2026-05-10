import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel
import BEDC.GroundCompiler.MainTheorems

/-!
# TasteGate framework (schema-enforced)

`BHistCarrier X` forces a chapter to commit to a specific BHist embedding
of its tokens before it can claim a TasteGate instance. `ChapterTasteGate
X` then states four obligations whose statements all reference `X` and the
embedding fields, so a chapter cannot supply a vacuous proof that omits
its own carrier.

The earlier draft used a propositional structure where each chapter could
supply its own `Prop` field — that allowed vacuous witnesses (such as
`∀ n : Nat, n = n`) and offered no quality control. This module replaces
that schema with carrier-pinned obligations.
-/

namespace BEDC.GroundCompiler.TasteGate

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.MainTheorems

/-- Embedding of a chapter carrier into the BEDC ground EventFlow.

A chapter must give a finite-history embedding of `X` into `EventFlow`
together with a partial inverse. The `round_trip` field of
`ChapterTasteGate` then forces these to form a left inverse pair, so the
chapter cannot pretend to have a carrier it does not actually display. -/
class BHistCarrier (X : Type) where
  toEventFlow : X → EventFlow
  fromEventFlow : EventFlow → Option X

/-- The schema-enforced taste gate. Every obligation is parametrised by
`X` and (where relevant) by `BHistCarrier.toEventFlow` /
`BHistCarrier.fromEventFlow`, so a chapter cannot supply a vacuous
proposition that omits its own carrier. -/
class ChapterTasteGate (X : Type) [BHistCarrier X] where
  conservativity :
    ∀ (x : X) (w : RawEvent) (m : DisplayAlphabet),
      List.Mem w (BHistCarrier.toEventFlow x) →
      List.Mem m w →
      m = BMark.b0 ∨ m = BMark.b1
  no_hidden_input :
    ∀ (x : X), ∃ (e : EventFlow), BHistCarrier.fromEventFlow e = some x
  round_trip :
    ∀ (x : X),
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x
  layer_separation :
    ∀ (x y : X), x ≠ y →
      BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y

/-! ## Reference instance: the ground compiler chapter itself.

The ground compiler's own chapter naturally satisfies the gate. The
carrier is `EventFlow` itself, displayed as the identity, with
`event_flow_conservativity` discharging the conservativity obligation
and `rfl` discharging the round-trip and no-hidden-input obligations. -/

instance groundCompilerBHistCarrier : BHistCarrier EventFlow where
  toEventFlow := id
  fromEventFlow := fun e => some e

instance groundCompilerChapterTasteGate : ChapterTasteGate EventFlow where
  conservativity := by
    intro x w m hw hm
    exact event_flow_conservativity hw hm
  no_hidden_input := by
    intro x
    exact ⟨x, rfl⟩
  round_trip := by
    intro _
    rfl
  layer_separation := by
    intro x y hxy heq
    apply hxy
    exact heq

/-- Public alias preserved for backward compatibility with paper markers. -/
def groundCompilerSelfTasteGate : ChapterTasteGate EventFlow :=
  groundCompilerChapterTasteGate

end BEDC.GroundCompiler.TasteGate
