import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossHistCausalRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossHistCausalRouteUp : Type where
  | mk :
      (observerA observerB causalRoute maxRate observerSource observerGate continuation
        transport accessRoutes provenance localName : BHist) →
      CrossHistCausalRouteUp
  deriving DecidableEq

def crossHistCausalRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: crossHistCausalRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: crossHistCausalRouteEncodeBHist h

def crossHistCausalRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (crossHistCausalRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (crossHistCausalRouteDecodeBHist tail)

private theorem crossHistCausalRoute_decode_encode_bhist :
    ∀ h : BHist,
      crossHistCausalRouteDecodeBHist (crossHistCausalRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def crossHistCausalRouteFields : CrossHistCausalRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate observerSource
      observerGate continuation transport accessRoutes provenance localName =>
      [observerA, observerB, causalRoute, maxRate, observerSource, observerGate,
        continuation, transport, accessRoutes, provenance, localName]

def crossHistCausalRouteToEventFlow : CrossHistCausalRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate observerSource
      observerGate continuation transport accessRoutes provenance localName =>
      [[BMark.b0],
        crossHistCausalRouteEncodeBHist observerA,
        [BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist observerB,
        [BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist causalRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist maxRate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist observerSource,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist observerGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        crossHistCausalRouteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist accessRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRouteEncodeBHist localName]

def crossHistCausalRouteFromEventFlow :
    EventFlow → Option CrossHistCausalRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerA :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observerB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | causalRoute :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | maxRate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | observerSource :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | observerGate :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | accessRoutes ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | localName ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CrossHistCausalRouteUp.mk
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    observerA)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    observerB)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    causalRoute)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    maxRate)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    observerSource)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    observerGate)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    continuation)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    transport)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    accessRoutes)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    provenance)
                                                                                                  (crossHistCausalRouteDecodeBHist
                                                                                                    localName))
                                                                                          | _ :: _ => none

private theorem crossHistCausalRoute_round_trip :
    ∀ x : CrossHistCausalRouteUp,
      crossHistCausalRouteFromEventFlow (crossHistCausalRouteToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerA observerB causalRoute maxRate observerSource observerGate continuation
      transport accessRoutes provenance localName =>
      change
        some
          (CrossHistCausalRouteUp.mk
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist observerA))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist observerB))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist causalRoute))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist maxRate))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist observerSource))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist observerGate))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist continuation))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist transport))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist accessRoutes))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist provenance))
            (crossHistCausalRouteDecodeBHist
              (crossHistCausalRouteEncodeBHist localName))) =
          some
            (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
              observerSource observerGate continuation transport accessRoutes provenance
              localName)
      rw [crossHistCausalRoute_decode_encode_bhist observerA,
        crossHistCausalRoute_decode_encode_bhist observerB,
        crossHistCausalRoute_decode_encode_bhist causalRoute,
        crossHistCausalRoute_decode_encode_bhist maxRate,
        crossHistCausalRoute_decode_encode_bhist observerSource,
        crossHistCausalRoute_decode_encode_bhist observerGate,
        crossHistCausalRoute_decode_encode_bhist continuation,
        crossHistCausalRoute_decode_encode_bhist transport,
        crossHistCausalRoute_decode_encode_bhist accessRoutes,
        crossHistCausalRoute_decode_encode_bhist provenance,
        crossHistCausalRoute_decode_encode_bhist localName]

private theorem crossHistCausalRouteToEventFlow_injective
    {x y : CrossHistCausalRouteUp} :
    crossHistCausalRouteToEventFlow x =
      crossHistCausalRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      crossHistCausalRouteFromEventFlow (crossHistCausalRouteToEventFlow x) =
        crossHistCausalRouteFromEventFlow (crossHistCausalRouteToEventFlow y) :=
    congrArg crossHistCausalRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (crossHistCausalRoute_round_trip x).symm
      (Eq.trans hread (crossHistCausalRoute_round_trip y)))

private theorem CrossHistCausalRouteTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CrossHistCausalRouteUp,
      crossHistCausalRouteFields x = crossHistCausalRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observerA observerB causalRoute maxRate observerSource observerGate continuation
      transport accessRoutes provenance localName =>
      cases y with
      | mk observerA' observerB' causalRoute' maxRate' observerSource' observerGate'
          continuation' transport' accessRoutes' provenance' localName' =>
          cases hfields
          rfl

instance crossHistCausalRouteBHistCarrier :
    BHistCarrier CrossHistCausalRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := crossHistCausalRouteToEventFlow
  fromEventFlow := crossHistCausalRouteFromEventFlow

instance crossHistCausalRouteChapterTasteGate :
    ChapterTasteGate CrossHistCausalRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change crossHistCausalRouteFromEventFlow (crossHistCausalRouteToEventFlow x) = some x
    exact crossHistCausalRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (crossHistCausalRouteToEventFlow_injective heq)

instance crossHistCausalRouteFieldFaithful :
    FieldFaithful CrossHistCausalRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := crossHistCausalRouteFields
  field_faithful := CrossHistCausalRouteTasteGate_single_carrier_alignment_field_faithful

instance crossHistCausalRouteNontrivial : Nontrivial CrossHistCausalRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CrossHistCausalRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CrossHistCausalRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CrossHistCausalRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  crossHistCausalRouteChapterTasteGate

theorem CrossHistCausalRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      crossHistCausalRouteDecodeBHist (crossHistCausalRouteEncodeBHist h) = h) ∧
      (∀ x : CrossHistCausalRouteUp,
        crossHistCausalRouteFromEventFlow (crossHistCausalRouteToEventFlow x) = some x) ∧
        (∀ x y : CrossHistCausalRouteUp,
          crossHistCausalRouteToEventFlow x = crossHistCausalRouteToEventFlow y →
            x = y) ∧
          crossHistCausalRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact crossHistCausalRoute_decode_encode_bhist
  · constructor
    · exact crossHistCausalRoute_round_trip
    · constructor
      · intro x y heq
        exact crossHistCausalRouteToEventFlow_injective heq
      · rfl

theorem CrossHistCausalRouteCarrier_maximum_rate_gate :
    (∀ (ef : EventFlow) (x : CrossHistCausalRouteUp),
      crossHistCausalRouteFromEventFlow ef = some x →
        crossHistCausalRouteFromEventFlow
          (List.append ef ([[BMark.b0]] : EventFlow)) = none) ∧
      (∀ observerA observerB causalRoute maxRate observerSource observerGate continuation
          transport accessRoutes provenance localName extra : BHist,
        crossHistCausalRouteFromEventFlow
          (List.append
            (crossHistCausalRouteToEventFlow
              (CrossHistCausalRouteUp.mk observerA observerB causalRoute maxRate
                observerSource observerGate continuation transport accessRoutes provenance
                localName))
            [crossHistCausalRouteEncodeBHist extra]) = none) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro ef x hread
    cases ef with
    | nil =>
        cases hread
    | cons tag0 rest0 =>
        cases rest0 with
        | nil =>
            cases hread
        | cons observerA rest1 =>
            cases rest1 with
            | nil =>
                cases hread
            | cons tag1 rest2 =>
                cases rest2 with
                | nil =>
                    cases hread
                | cons observerB rest3 =>
                    cases rest3 with
                    | nil =>
                        cases hread
                    | cons tag2 rest4 =>
                        cases rest4 with
                        | nil =>
                            cases hread
                        | cons causalRoute rest5 =>
                            cases rest5 with
                            | nil =>
                                cases hread
                            | cons tag3 rest6 =>
                                cases rest6 with
                                | nil =>
                                    cases hread
                                | cons maxRate rest7 =>
                                    cases rest7 with
                                    | nil =>
                                        cases hread
                                    | cons tag4 rest8 =>
                                        cases rest8 with
                                        | nil =>
                                            cases hread
                                        | cons observerSource rest9 =>
                                            cases rest9 with
                                            | nil =>
                                                cases hread
                                            | cons tag5 rest10 =>
                                                cases rest10 with
                                                | nil =>
                                                    cases hread
                                                | cons observerGate rest11 =>
                                                    cases rest11 with
                                                    | nil =>
                                                        cases hread
                                                    | cons tag6 rest12 =>
                                                        cases rest12 with
                                                        | nil =>
                                                            cases hread
                                                        | cons continuation rest13 =>
                                                            cases rest13 with
                                                            | nil =>
                                                                cases hread
                                                            | cons tag7 rest14 =>
                                                                cases rest14 with
                                                                | nil =>
                                                                    cases hread
                                                                | cons transport rest15 =>
                                                                    cases rest15 with
                                                                    | nil =>
                                                                        cases hread
                                                                    | cons tag8 rest16 =>
                                                                        cases rest16 with
                                                                        | nil =>
                                                                            cases hread
                                                                        | cons accessRoutes rest17 =>
                                                                            cases rest17 with
                                                                            | nil =>
                                                                                cases hread
                                                                            | cons tag9 rest18 =>
                                                                                cases rest18 with
                                                                                | nil =>
                                                                                    cases hread
                                                                                | cons provenance rest19 =>
                                                                                    cases rest19 with
                                                                                    | nil =>
                                                                                        cases hread
                                                                                    | cons tag10 rest20 =>
                                                                                        cases rest20 with
                                                                                        | nil =>
                                                                                            cases hread
                                                                                        | cons localName rest21 =>
                                                                                            cases rest21 with
                                                                                            | nil =>
                                                                                                rfl
                                                                                            | cons extra rest22 =>
                                                                                                cases hread
  · intro observerA observerB causalRoute maxRate observerSource observerGate continuation
      transport accessRoutes provenance localName extra
    rfl

end BEDC.Derived.CrossHistCausalRouteUp
