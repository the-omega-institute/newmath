import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICFuelTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICFuelTraceUp : Type where
  | mk :
      (fuel input output endpoint equalityCheck boundedConversion refusal transport replay
        provenance name : BHist) ->
      MetaCICFuelTraceUp
  deriving DecidableEq

def metacicFuelTraceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicFuelTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicFuelTraceEncodeBHist h

def metacicFuelTraceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicFuelTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicFuelTraceDecodeBHist tail)

private theorem metacicFuelTraceDecode_encode_bhist :
    forall h : BHist, metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicFuelTraceToEventFlow : MetaCICFuelTraceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICFuelTraceUp.mk fuel input output endpoint equalityCheck boundedConversion refusal
      transport replay provenance name =>
      [[BMark.b0],
        metacicFuelTraceEncodeBHist fuel,
        [BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist input,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist equalityCheck,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist boundedConversion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicFuelTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicFuelTraceEncodeBHist name]

private def metacicFuelTraceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metacicFuelTraceEventAtDefault index rest

def metacicFuelTraceFromEventFlow (ef : EventFlow) : Option MetaCICFuelTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICFuelTraceUp.mk
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 1 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 3 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 5 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 7 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 9 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 11 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 13 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 15 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 17 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 19 ef))
      (metacicFuelTraceDecodeBHist (metacicFuelTraceEventAtDefault 21 ef)))

private theorem metacicFuelTrace_round_trip :
    forall x : MetaCICFuelTraceUp,
      metacicFuelTraceFromEventFlow (metacicFuelTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel input output endpoint equalityCheck boundedConversion refusal transport replay
      provenance name =>
      change
        some
          (MetaCICFuelTraceUp.mk
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist fuel))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist input))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist output))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist endpoint))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist equalityCheck))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist boundedConversion))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist refusal))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist transport))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist replay))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist provenance))
            (metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist name))) =
          some
            (MetaCICFuelTraceUp.mk fuel input output endpoint equalityCheck boundedConversion
              refusal transport replay provenance name)
      rw [metacicFuelTraceDecode_encode_bhist fuel,
        metacicFuelTraceDecode_encode_bhist input,
        metacicFuelTraceDecode_encode_bhist output,
        metacicFuelTraceDecode_encode_bhist endpoint,
        metacicFuelTraceDecode_encode_bhist equalityCheck,
        metacicFuelTraceDecode_encode_bhist boundedConversion,
        metacicFuelTraceDecode_encode_bhist refusal,
        metacicFuelTraceDecode_encode_bhist transport,
        metacicFuelTraceDecode_encode_bhist replay,
        metacicFuelTraceDecode_encode_bhist provenance,
        metacicFuelTraceDecode_encode_bhist name]

private theorem metacicFuelTraceToEventFlow_injective {x y : MetaCICFuelTraceUp} :
    metacicFuelTraceToEventFlow x = metacicFuelTraceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicFuelTraceFromEventFlow (metacicFuelTraceToEventFlow x) =
        metacicFuelTraceFromEventFlow (metacicFuelTraceToEventFlow y) :=
    congrArg metacicFuelTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicFuelTrace_round_trip x).symm
      (Eq.trans hread (metacicFuelTrace_round_trip y)))

def metacicFuelTraceFields : MetaCICFuelTraceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICFuelTraceUp.mk fuel input output endpoint equalityCheck boundedConversion refusal
      transport replay provenance name =>
      [fuel, input, output, endpoint, equalityCheck, boundedConversion, refusal, transport,
        replay, provenance, name]

private theorem metacicFuelTrace_fields_faithful :
    forall x y : MetaCICFuelTraceUp,
      metacicFuelTraceFields x = metacicFuelTraceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fuel input output endpoint equalityCheck boundedConversion refusal transport replay
      provenance name =>
      cases y with
      | mk fuel' input' output' endpoint' equalityCheck' boundedConversion' refusal'
          transport' replay' provenance' name' =>
          injection hfields with hFuel hRest1
          injection hRest1 with hInput hRest2
          injection hRest2 with hOutput hRest3
          injection hRest3 with hEndpoint hRest4
          injection hRest4 with hEqualityCheck hRest5
          injection hRest5 with hBoundedConversion hRest6
          injection hRest6 with hRefusal hRest7
          injection hRest7 with hTransport hRest8
          injection hRest8 with hReplay hRest9
          injection hRest9 with hProvenance hRest10
          injection hRest10 with hName _
          subst hFuel
          subst hInput
          subst hOutput
          subst hEndpoint
          subst hEqualityCheck
          subst hBoundedConversion
          subst hRefusal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance metacicFuelTraceBHistCarrier : BHistCarrier MetaCICFuelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicFuelTraceToEventFlow
  fromEventFlow := metacicFuelTraceFromEventFlow

instance metacicFuelTraceChapterTasteGate : ChapterTasteGate MetaCICFuelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metacicFuelTraceFromEventFlow (metacicFuelTraceToEventFlow x) = some x
    exact metacicFuelTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicFuelTraceToEventFlow_injective heq)

instance metacicFuelTraceFieldFaithful : FieldFaithful MetaCICFuelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicFuelTraceFields
  field_faithful := metacicFuelTrace_fields_faithful

instance metacicFuelTraceNontrivial : Nontrivial MetaCICFuelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICFuelTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICFuelTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaCICFuelTraceTasteGate_single_carrier_alignment :
    (forall h : BHist, metacicFuelTraceDecodeBHist (metacicFuelTraceEncodeBHist h) = h) /\
      (forall x : MetaCICFuelTraceUp,
        metacicFuelTraceFromEventFlow (metacicFuelTraceToEventFlow x) = some x) /\
        (forall x y : MetaCICFuelTraceUp,
          metacicFuelTraceToEventFlow x = metacicFuelTraceToEventFlow y -> x = y) /\
          metacicFuelTraceFields
              (MetaCICFuelTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicFuelTraceDecode_encode_bhist
  · constructor
    · exact metacicFuelTrace_round_trip
    · constructor
      · intro x y heq
        exact metacicFuelTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICFuelTraceUp
