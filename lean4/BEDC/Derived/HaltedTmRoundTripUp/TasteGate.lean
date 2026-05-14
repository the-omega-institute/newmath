import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltedTmRoundTripUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltedTmRoundTripUp : Type where
  | mk :
      (machine input haltedTrace encoding decoding transport route provenance localName :
        BHist) →
        HaltedTmRoundTripUp
  deriving DecidableEq

def haltedTmRoundTripEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltedTmRoundTripEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltedTmRoundTripEncodeBHist h

def haltedTmRoundTripDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltedTmRoundTripDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltedTmRoundTripDecodeBHist tail)

private theorem HaltedTmRoundTripTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      haltedTmRoundTripDecodeBHist
        (haltedTmRoundTripEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def haltedTmRoundTripToEventFlow :
    HaltedTmRoundTripUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltedTmRoundTripUp.mk machine input haltedTrace encoding decoding transport route
      provenance localName =>
      [[BMark.b0],
        haltedTmRoundTripEncodeBHist machine,
        [BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist input,
        [BMark.b1, BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist haltedTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist encoding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist decoding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltedTmRoundTripEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        haltedTmRoundTripEncodeBHist localName]

def haltedTmRoundTripFromEventFlow :
    EventFlow → Option HaltedTmRoundTripUp
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
              | input :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | haltedTrace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | encoding :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | decoding :: rest9 =>
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
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (HaltedTmRoundTripUp.mk
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    machine)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    input)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    haltedTrace)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    encoding)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    decoding)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    transport)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    route)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    provenance)
                                                                                  (haltedTmRoundTripDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem HaltedTmRoundTripTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HaltedTmRoundTripUp,
      haltedTmRoundTripFromEventFlow
        (haltedTmRoundTripToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk machine input haltedTrace encoding decoding transport route provenance localName =>
      change
        some
          (HaltedTmRoundTripUp.mk
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist machine))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist input))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist haltedTrace))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist encoding))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist decoding))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist transport))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist route))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist provenance))
            (haltedTmRoundTripDecodeBHist
              (haltedTmRoundTripEncodeBHist localName))) =
          some
            (HaltedTmRoundTripUp.mk machine input haltedTrace encoding decoding
              transport route provenance localName)
      rw [HaltedTmRoundTripTasteGate_single_carrier_alignment_decode machine,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode input,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode haltedTrace,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode encoding,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode decoding,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode transport,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode route,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode provenance,
        HaltedTmRoundTripTasteGate_single_carrier_alignment_decode localName]

private theorem HaltedTmRoundTripTasteGate_single_carrier_alignment_injective
    {x y : HaltedTmRoundTripUp} :
    haltedTmRoundTripToEventFlow x =
      haltedTmRoundTripToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltedTmRoundTripFromEventFlow (haltedTmRoundTripToEventFlow x) =
        haltedTmRoundTripFromEventFlow (haltedTmRoundTripToEventFlow y) :=
    congrArg haltedTmRoundTripFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HaltedTmRoundTripTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HaltedTmRoundTripTasteGate_single_carrier_alignment_round_trip y)))

instance haltedTmRoundTripBHistCarrier :
    BHistCarrier HaltedTmRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltedTmRoundTripToEventFlow
  fromEventFlow := haltedTmRoundTripFromEventFlow

instance haltedTmRoundTripChapterTasteGate :
    ChapterTasteGate HaltedTmRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      haltedTmRoundTripFromEventFlow
        (haltedTmRoundTripToEventFlow x) = some x
    exact HaltedTmRoundTripTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HaltedTmRoundTripTasteGate_single_carrier_alignment_injective heq)

instance haltedTmRoundTripFieldFaithful :
    FieldFaithful HaltedTmRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | HaltedTmRoundTripUp.mk machine input haltedTrace encoding decoding transport route
        provenance localName =>
        [machine, input, haltedTrace, encoding, decoding, transport, route, provenance,
          localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk machine1 input1 haltedTrace1 encoding1 decoding1 transport1 route1 provenance1
        localName1 =>
        cases y with
        | mk machine2 input2 haltedTrace2 encoding2 decoding2 transport2 route2 provenance2
            localName2 =>
            cases h
            rfl

instance haltedTmRoundTripNontrivial :
    Nontrivial HaltedTmRoundTripUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HaltedTmRoundTripUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HaltedTmRoundTripUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HaltedTmRoundTripUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltedTmRoundTripChapterTasteGate

theorem HaltedTmRoundTripTasteGate_single_carrier_alignment :
    (∀ h : BHist, haltedTmRoundTripDecodeBHist
      (haltedTmRoundTripEncodeBHist h) = h) ∧
      (∀ x : HaltedTmRoundTripUp, haltedTmRoundTripFromEventFlow
        (haltedTmRoundTripToEventFlow x) = some x) ∧
        (∀ x y : HaltedTmRoundTripUp,
          haltedTmRoundTripToEventFlow x =
            haltedTmRoundTripToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate HaltedTmRoundTripUp) ∧
            Nonempty (FieldFaithful HaltedTmRoundTripUp) ∧
              Nonempty (Nontrivial HaltedTmRoundTripUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HaltedTmRoundTripTasteGate_single_carrier_alignment_decode
  · constructor
    · exact HaltedTmRoundTripTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HaltedTmRoundTripTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨haltedTmRoundTripChapterTasteGate⟩,
            ⟨haltedTmRoundTripFieldFaithful⟩,
            ⟨haltedTmRoundTripNontrivial⟩⟩

end BEDC.Derived.HaltedTmRoundTripUp.TasteGate

namespace BEDC.Derived.HaltedTmRoundTripUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.HaltedTmRoundTripUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.HaltedTmRoundTripUp
