import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingTraceClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingTraceClassifierUp : Type where
  | mk (machine history trace classifier refusal transport routes provenance name : BHist) :
      HaltingTraceClassifierUp
  deriving DecidableEq

private def haltingTraceClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingTraceClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingTraceClassifierEncodeBHist h

private def haltingTraceClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingTraceClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingTraceClassifierDecodeBHist tail)

private theorem haltingTraceClassifier_decode_encode_bhist :
    ∀ h : BHist,
      haltingTraceClassifierDecodeBHist (haltingTraceClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def haltingTraceClassifierToEventFlow : HaltingTraceClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingTraceClassifierUp.mk machine history trace classifier refusal transport routes
      provenance name =>
      [[BMark.b0],
        haltingTraceClassifierEncodeBHist machine,
        [BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltingTraceClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist name]

private def haltingTraceClassifierDecodePacket
    (machine history trace classifier refusal transport routes provenance name : RawEvent) :
    HaltingTraceClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HaltingTraceClassifierUp.mk
    (haltingTraceClassifierDecodeBHist machine)
    (haltingTraceClassifierDecodeBHist history)
    (haltingTraceClassifierDecodeBHist trace)
    (haltingTraceClassifierDecodeBHist classifier)
    (haltingTraceClassifierDecodeBHist refusal)
    (haltingTraceClassifierDecodeBHist transport)
    (haltingTraceClassifierDecodeBHist routes)
    (haltingTraceClassifierDecodeBHist provenance)
    (haltingTraceClassifierDecodeBHist name)

private def haltingTraceClassifierFromEventFlow :
    EventFlow → Option HaltingTraceClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | machine :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | history :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | trace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (haltingTraceClassifierDecodePacket
                                                                                  machine
                                                                                  history
                                                                                  trace
                                                                                  classifier
                                                                                  refusal
                                                                                  transport
                                                                                  routes
                                                                                  provenance
                                                                                  name)
                                                                          | _ :: _ => none

private theorem haltingTraceClassifier_round_trip :
    ∀ x : HaltingTraceClassifierUp,
      haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk machine history trace classifier refusal transport routes provenance name =>
      change
        some
          (haltingTraceClassifierDecodePacket
            (haltingTraceClassifierEncodeBHist machine)
            (haltingTraceClassifierEncodeBHist history)
            (haltingTraceClassifierEncodeBHist trace)
            (haltingTraceClassifierEncodeBHist classifier)
            (haltingTraceClassifierEncodeBHist refusal)
            (haltingTraceClassifierEncodeBHist transport)
            (haltingTraceClassifierEncodeBHist routes)
            (haltingTraceClassifierEncodeBHist provenance)
            (haltingTraceClassifierEncodeBHist name)) =
          some
            (HaltingTraceClassifierUp.mk machine history trace classifier refusal transport
              routes provenance name)
      unfold haltingTraceClassifierDecodePacket
      rw [haltingTraceClassifier_decode_encode_bhist machine,
        haltingTraceClassifier_decode_encode_bhist history,
        haltingTraceClassifier_decode_encode_bhist trace,
        haltingTraceClassifier_decode_encode_bhist classifier,
        haltingTraceClassifier_decode_encode_bhist refusal,
        haltingTraceClassifier_decode_encode_bhist transport,
        haltingTraceClassifier_decode_encode_bhist routes,
        haltingTraceClassifier_decode_encode_bhist provenance,
        haltingTraceClassifier_decode_encode_bhist name]

private theorem haltingTraceClassifierToEventFlow_injective
    {x y : HaltingTraceClassifierUp} :
    haltingTraceClassifierToEventFlow x = haltingTraceClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow x) =
        haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow y) :=
    congrArg haltingTraceClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingTraceClassifier_round_trip x).symm
      (Eq.trans hread (haltingTraceClassifier_round_trip y)))

private def haltingTraceClassifierFields : HaltingTraceClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingTraceClassifierUp.mk machine history trace classifier refusal transport routes
      provenance name =>
      [machine, history, trace, classifier, refusal, transport, routes, provenance, name]

private theorem haltingTraceClassifier_field_faithful :
    ∀ x y : HaltingTraceClassifierUp,
      haltingTraceClassifierFields x = haltingTraceClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk machine history trace classifier refusal transport routes provenance name =>
      cases y with
      | mk machine' history' trace' classifier' refusal' transport' routes' provenance'
          name' =>
          cases hfields
          rfl

instance haltingTraceClassifierBHistCarrier :
    BHistCarrier HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingTraceClassifierToEventFlow
  fromEventFlow := haltingTraceClassifierFromEventFlow

instance haltingTraceClassifierChapterTasteGate :
    ChapterTasteGate HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow x) = some x
    exact haltingTraceClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingTraceClassifierToEventFlow_injective heq)

instance haltingTraceClassifierFieldFaithful :
    FieldFaithful HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := haltingTraceClassifierFields
  field_faithful := haltingTraceClassifier_field_faithful

instance haltingTraceClassifierNontrivial :
    Nontrivial HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HaltingTraceClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HaltingTraceClassifierUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HaltingTraceClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltingTraceClassifierChapterTasteGate

theorem HaltingTraceClassifierUp_taste_gate_boundary :
    (∀ x : HaltingTraceClassifierUp, ∃ e : EventFlow,
      BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : HaltingTraceClassifierUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ChapterTasteGate.no_hidden_input
  · exact ChapterTasteGate.conservativity

end BEDC.Derived.HaltingTraceClassifierUp
