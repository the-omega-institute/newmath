import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryWindowSealExhaustionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryWindowSealExhaustionUp : Type where
  | mk :
      (ratSeed streamWindow regularSeal dyadicLedger realSeal exhaustion transport
        continuation provenance localName : BHist) →
        StationaryWindowSealExhaustionUp
  deriving DecidableEq

def stationaryWindowSealExhaustionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryWindowSealExhaustionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryWindowSealExhaustionEncodeBHist h

def stationaryWindowSealExhaustionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryWindowSealExhaustionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryWindowSealExhaustionDecodeBHist tail)

private theorem StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      stationaryWindowSealExhaustionDecodeBHist
        (stationaryWindowSealExhaustionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stationaryWindowSealExhaustionToEventFlow :
    StationaryWindowSealExhaustionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryWindowSealExhaustionUp.mk ratSeed streamWindow regularSeal dyadicLedger
      realSeal exhaustion transport continuation provenance localName =>
      [[BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist ratSeed,
        [BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist regularSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist exhaustion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowSealExhaustionEncodeBHist localName]

def stationaryWindowSealExhaustionFromEventFlow :
    EventFlow → Option StationaryWindowSealExhaustionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | ratSeed :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | streamWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regularSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadicLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | exhaustion :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (StationaryWindowSealExhaustionUp.mk
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            ratSeed)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            streamWindow)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            regularSeal)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            dyadicLedger)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            realSeal)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            exhaustion)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            transport)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            continuation)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            provenance)
                                                                                          (stationaryWindowSealExhaustionDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StationaryWindowSealExhaustionUp,
      stationaryWindowSealExhaustionFromEventFlow
        (stationaryWindowSealExhaustionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ratSeed streamWindow regularSeal dyadicLedger realSeal exhaustion transport
      continuation provenance localName =>
      change
        some
          (StationaryWindowSealExhaustionUp.mk
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist ratSeed))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist streamWindow))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist regularSeal))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist dyadicLedger))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist realSeal))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist exhaustion))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist transport))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist continuation))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist provenance))
            (stationaryWindowSealExhaustionDecodeBHist
              (stationaryWindowSealExhaustionEncodeBHist localName))) =
          some
            (StationaryWindowSealExhaustionUp.mk ratSeed streamWindow regularSeal
              dyadicLedger realSeal exhaustion transport continuation provenance localName)
      rw [StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode ratSeed,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode streamWindow,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode regularSeal,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode dyadicLedger,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode realSeal,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode exhaustion,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode transport,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode continuation,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode provenance,
        StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode localName]

private theorem StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_injective
    {x y : StationaryWindowSealExhaustionUp} :
    stationaryWindowSealExhaustionToEventFlow x =
      stationaryWindowSealExhaustionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryWindowSealExhaustionFromEventFlow
          (stationaryWindowSealExhaustionToEventFlow x) =
        stationaryWindowSealExhaustionFromEventFlow
          (stationaryWindowSealExhaustionToEventFlow y) :=
    congrArg stationaryWindowSealExhaustionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_round_trip y)))

instance stationaryWindowSealExhaustionBHistCarrier :
    BHistCarrier StationaryWindowSealExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryWindowSealExhaustionToEventFlow
  fromEventFlow := stationaryWindowSealExhaustionFromEventFlow

instance stationaryWindowSealExhaustionChapterTasteGate :
    ChapterTasteGate StationaryWindowSealExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryWindowSealExhaustionFromEventFlow
        (stationaryWindowSealExhaustionToEventFlow x) = some x
    exact StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_injective heq)

instance stationaryWindowSealExhaustionFieldFaithful :
    FieldFaithful StationaryWindowSealExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | StationaryWindowSealExhaustionUp.mk ratSeed streamWindow regularSeal dyadicLedger
        realSeal exhaustion transport continuation provenance localName =>
        [ratSeed, streamWindow, regularSeal, dyadicLedger, realSeal, exhaustion, transport,
          continuation, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk ratSeed1 streamWindow1 regularSeal1 dyadicLedger1 realSeal1 exhaustion1 transport1
        continuation1 provenance1 localName1 =>
        cases y with
        | mk ratSeed2 streamWindow2 regularSeal2 dyadicLedger2 realSeal2 exhaustion2
            transport2 continuation2 provenance2 localName2 =>
            cases h
            rfl

instance stationaryWindowSealExhaustionNontrivial :
    Nontrivial StationaryWindowSealExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StationaryWindowSealExhaustionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StationaryWindowSealExhaustionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StationaryWindowSealExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stationaryWindowSealExhaustionChapterTasteGate

theorem StationaryWindowSealExhaustionTasteGate_single_carrier_alignment :
    (∀ h : BHist, stationaryWindowSealExhaustionDecodeBHist
      (stationaryWindowSealExhaustionEncodeBHist h) = h) ∧
      (∀ x : StationaryWindowSealExhaustionUp, stationaryWindowSealExhaustionFromEventFlow
        (stationaryWindowSealExhaustionToEventFlow x) = some x) ∧
        (∀ x y : StationaryWindowSealExhaustionUp,
          stationaryWindowSealExhaustionToEventFlow x =
            stationaryWindowSealExhaustionToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate StationaryWindowSealExhaustionUp) ∧
            Nonempty (FieldFaithful StationaryWindowSealExhaustionUp) ∧
              Nonempty (Nontrivial StationaryWindowSealExhaustionUp) ∧
                stationaryWindowSealExhaustionEncodeBHist (BHist.e0 BHist.Empty) =
                  [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact StationaryWindowSealExhaustionTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨stationaryWindowSealExhaustionChapterTasteGate⟩,
            ⟨stationaryWindowSealExhaustionFieldFaithful⟩,
            ⟨stationaryWindowSealExhaustionNontrivial⟩,
            rfl⟩

end BEDC.Derived.StationaryWindowSealExhaustionUp.TasteGate

namespace BEDC.Derived.StationaryWindowSealExhaustionUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.StationaryWindowSealExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.StationaryWindowSealExhaustionUp
