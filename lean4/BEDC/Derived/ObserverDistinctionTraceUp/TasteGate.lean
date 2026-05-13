import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverDistinctionTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverDistinctionTraceUp : Type where
  | mk :
      (source trace growth routes transport provenance localName : BHist) →
      ObserverDistinctionTraceUp
  deriving DecidableEq

def observerDistinctionTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerDistinctionTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerDistinctionTraceEncodeBHist h

def observerDistinctionTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerDistinctionTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerDistinctionTraceDecodeBHist tail)

private theorem observerDistinctionTrace_decode_encode_bhist :
    ∀ h : BHist,
      observerDistinctionTraceDecodeBHist (observerDistinctionTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerDistinctionTraceFields : ObserverDistinctionTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
      localName =>
      [source, trace, growth, routes, transport, provenance, localName]

def observerDistinctionTraceToEventFlow : ObserverDistinctionTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
      localName =>
      [[BMark.b0],
        observerDistinctionTraceEncodeBHist source,
        [BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist growth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist localName]

def observerDistinctionTraceFromEventFlow :
    EventFlow → Option ObserverDistinctionTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | growth :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (ObserverDistinctionTraceUp.mk
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    source)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    trace)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    growth)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    routes)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    transport)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    provenance)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    localName))
                                                          | _ :: _ => none

private theorem observerDistinctionTrace_round_trip :
    ∀ x : ObserverDistinctionTraceUp,
      observerDistinctionTraceFromEventFlow
        (observerDistinctionTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source trace growth routes transport provenance localName =>
      change
        some
          (ObserverDistinctionTraceUp.mk
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist source))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist trace))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist growth))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist routes))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist transport))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist provenance))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist localName))) =
          some
            (ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
              localName)
      rw [observerDistinctionTrace_decode_encode_bhist source,
        observerDistinctionTrace_decode_encode_bhist trace,
        observerDistinctionTrace_decode_encode_bhist growth,
        observerDistinctionTrace_decode_encode_bhist routes,
        observerDistinctionTrace_decode_encode_bhist transport,
        observerDistinctionTrace_decode_encode_bhist provenance,
        observerDistinctionTrace_decode_encode_bhist localName]

private theorem observerDistinctionTraceToEventFlow_injective
    {x y : ObserverDistinctionTraceUp} :
    observerDistinctionTraceToEventFlow x =
      observerDistinctionTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerDistinctionTraceFromEventFlow (observerDistinctionTraceToEventFlow x) =
        observerDistinctionTraceFromEventFlow (observerDistinctionTraceToEventFlow y) :=
    congrArg observerDistinctionTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerDistinctionTrace_round_trip x).symm
      (Eq.trans hread (observerDistinctionTrace_round_trip y)))

private theorem ObserverDistinctionTraceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ObserverDistinctionTraceUp,
      observerDistinctionTraceFields x = observerDistinctionTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source trace growth routes transport provenance localName =>
      cases y with
      | mk source' trace' growth' routes' transport' provenance' localName' =>
          cases hfields
          rfl

instance observerDistinctionTraceBHistCarrier :
    BHistCarrier ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerDistinctionTraceToEventFlow
  fromEventFlow := observerDistinctionTraceFromEventFlow

instance observerDistinctionTraceChapterTasteGate :
    ChapterTasteGate ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerDistinctionTraceFromEventFlow
        (observerDistinctionTraceToEventFlow x) = some x
    exact observerDistinctionTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerDistinctionTraceToEventFlow_injective heq)

instance observerDistinctionTraceFieldFaithful :
    FieldFaithful ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerDistinctionTraceFields
  field_faithful := ObserverDistinctionTraceTasteGate_single_carrier_alignment_field_faithful

instance observerDistinctionTraceNontrivial :
    Nontrivial ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverDistinctionTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObserverDistinctionTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverDistinctionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerDistinctionTraceChapterTasteGate

theorem ObserverDistinctionTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerDistinctionTraceDecodeBHist (observerDistinctionTraceEncodeBHist h) = h) ∧
      (∀ x : ObserverDistinctionTraceUp,
        observerDistinctionTraceFromEventFlow
          (observerDistinctionTraceToEventFlow x) = some x) ∧
        (∀ x y : ObserverDistinctionTraceUp,
          observerDistinctionTraceToEventFlow x =
            observerDistinctionTraceToEventFlow y → x = y) ∧
          observerDistinctionTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerDistinctionTrace_decode_encode_bhist
  · constructor
    · exact observerDistinctionTrace_round_trip
    · constructor
      · intro x y heq
        exact observerDistinctionTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverDistinctionTraceUp
