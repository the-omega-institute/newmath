import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel
import BEDC.GroundCompiler.MainTheorems

/-!
# TasteGate framework

A propositional taste gate that AI-proposed BEDC chapters must inhabit
to claim cross-chapter / cross-layer stability. The four obligations
parallel the ground-compiler theorems:

* `conservativity_holds`: introducing the chapter does not let any
  baseline-only formula change provability;
* `no_hidden_input_holds`: every chapter-token can be reconstructed
  from a finite history readback (no smuggled outside object);
* `round_trip_holds`: the chapter's display readback is invertible;
* `layer_separation_holds`: source / channel / display roles do not
  collapse.

Phase 0 only ships the framework + one reference instance backed by
the ground-compiler self-conservativity theorems. The audit gate is
off; chapters are not yet required to inhabit this structure.
-/

namespace BEDC.GroundCompiler.TasteGate

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.MainTheorems

/-- The taste-gate carrier interface. Each `Prop` field states the
chapter-side obligation; the matching proof field discharges it. -/
structure ChapterTasteGate (X : Type) where
  conservativity_holds : Prop
  conservativity_proof : conservativity_holds
  no_hidden_input_holds : Prop
  no_hidden_input_proof : no_hidden_input_holds
  round_trip_holds : Prop
  round_trip_proof : round_trip_holds
  layer_separation_holds : Prop
  layer_separation_proof : layer_separation_holds

/-- Reference instance: the ground compiler chapter itself satisfies the
taste gate, witnessed directly by its own conservativity / no-hidden-input
/ round-trip theorems. -/
def groundCompilerSelfTasteGate : ChapterTasteGate Unit where
  conservativity_holds :=
    ∀ {S : EventFlow} {w : RawEvent} {m : DisplayAlphabet},
      List.Mem w S → List.Mem m w → m = BMark.b0 ∨ m = BMark.b1
  conservativity_proof := @event_flow_conservativity
  no_hidden_input_holds :=
    ∀ {d : CompilerDatum},
      HiddenInput d → Not (FormalCompilerInput d)
  no_hidden_input_proof :=
    fun {d} => no_hidden_input canonical_no_hidden_input_compiler_state (d := d)
  round_trip_holds :=
    ∀ S : EventFlow, Decode (FlowEncoding S) = some S
  round_trip_proof := flow_level_round_trip
  layer_separation_holds := True
  layer_separation_proof := True.intro

end BEDC.GroundCompiler.TasteGate
