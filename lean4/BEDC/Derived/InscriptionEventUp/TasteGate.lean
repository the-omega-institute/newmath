import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionEventUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionEventUp : Type where
  | mk :
      (source name route check consumer gap transport routes provenance nameCert : BHist) →
      InscriptionEventUp
  deriving DecidableEq

def inscriptionEventEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionEventEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionEventEncodeBHist h

def inscriptionEventDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionEventDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionEventDecodeBHist tail)

private theorem inscriptionEventDecode_encode_bhist :
    ∀ h : BHist, inscriptionEventDecodeBHist (inscriptionEventEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionEventToEventFlow : InscriptionEventUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionEventUp.mk source name route check consumer gap transport routes provenance
      nameCert =>
      [[BMark.b0],
        inscriptionEventEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionEventEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventEncodeBHist nameCert]

def inscriptionEventFromEventFlow : EventFlow → Option InscriptionEventUp
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
              | name :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | check :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | consumer :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gap :: rest11 =>
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
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscriptionEventUp.mk
                                                                                          (inscriptionEventDecodeBHist source)
                                                                                          (inscriptionEventDecodeBHist name)
                                                                                          (inscriptionEventDecodeBHist route)
                                                                                          (inscriptionEventDecodeBHist check)
                                                                                          (inscriptionEventDecodeBHist consumer)
                                                                                          (inscriptionEventDecodeBHist gap)
                                                                                          (inscriptionEventDecodeBHist transport)
                                                                                          (inscriptionEventDecodeBHist routes)
                                                                                          (inscriptionEventDecodeBHist provenance)
                                                                                          (inscriptionEventDecodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem inscriptionEvent_round_trip :
    ∀ x : InscriptionEventUp,
      inscriptionEventFromEventFlow (inscriptionEventToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source name route check consumer gap transport routes provenance nameCert =>
      change
        some
          (InscriptionEventUp.mk
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist source))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist name))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist route))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist check))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist consumer))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist gap))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist transport))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist routes))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist provenance))
            (inscriptionEventDecodeBHist (inscriptionEventEncodeBHist nameCert))) =
          some
            (InscriptionEventUp.mk source name route check consumer gap transport routes
              provenance nameCert)
      rw [inscriptionEventDecode_encode_bhist source,
        inscriptionEventDecode_encode_bhist name,
        inscriptionEventDecode_encode_bhist route,
        inscriptionEventDecode_encode_bhist check,
        inscriptionEventDecode_encode_bhist consumer,
        inscriptionEventDecode_encode_bhist gap,
        inscriptionEventDecode_encode_bhist transport,
        inscriptionEventDecode_encode_bhist routes,
        inscriptionEventDecode_encode_bhist provenance,
        inscriptionEventDecode_encode_bhist nameCert]

private theorem inscriptionEventToEventFlow_injective {x y : InscriptionEventUp} :
    inscriptionEventToEventFlow x = inscriptionEventToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionEventFromEventFlow (inscriptionEventToEventFlow x) =
        inscriptionEventFromEventFlow (inscriptionEventToEventFlow y) :=
    congrArg inscriptionEventFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionEvent_round_trip x).symm
      (Eq.trans hread (inscriptionEvent_round_trip y)))

instance inscriptionEventBHistCarrier : BHistCarrier InscriptionEventUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionEventToEventFlow
  fromEventFlow := inscriptionEventFromEventFlow

instance inscriptionEventChapterTasteGate : ChapterTasteGate InscriptionEventUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscriptionEventFromEventFlow (inscriptionEventToEventFlow x) = some x
    exact inscriptionEvent_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionEventToEventFlow_injective heq)

theorem InscriptionEventTasteGate_single_carrier_alignment :
    (∀ h : BHist, inscriptionEventDecodeBHist (inscriptionEventEncodeBHist h) = h) ∧
      (∀ x : InscriptionEventUp,
        inscriptionEventFromEventFlow (inscriptionEventToEventFlow x) = some x) ∧
        (∀ x y : InscriptionEventUp,
          inscriptionEventToEventFlow x = inscriptionEventToEventFlow y → x = y) ∧
          inscriptionEventEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionEventDecode_encode_bhist
  · constructor
    · exact inscriptionEvent_round_trip
    · constructor
      · intro x y heq
        exact inscriptionEventToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscriptionEventUp
