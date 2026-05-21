import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TruthTotalReflectionUp : Type where
  | mk :
      (sentenceCodes extensionAttempt diagonal transport route provenance name : BHist) →
      TruthTotalReflectionUp
  deriving DecidableEq

private def truthTotalReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: truthTotalReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: truthTotalReflectionEncodeBHist h

private def truthTotalReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (truthTotalReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (truthTotalReflectionDecodeBHist tail)

private theorem truthTotalReflection_decode_encode_bhist :
    ∀ h : BHist, truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def truthTotalReflectionToEventFlow : TruthTotalReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TruthTotalReflectionUp.mk sentenceCodes extensionAttempt diagonal transport route
      provenance name =>
      [[BMark.b0],
        truthTotalReflectionEncodeBHist sentenceCodes,
        [BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist extensionAttempt,
        [BMark.b1, BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        truthTotalReflectionEncodeBHist name]

private def truthTotalReflectionFromEventFlow : EventFlow → Option TruthTotalReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sentenceCodes :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | extensionAttempt :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagonal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
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
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (TruthTotalReflectionUp.mk
                                                                  (truthTotalReflectionDecodeBHist
                                                                    sentenceCodes)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    extensionAttempt)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    diagonal)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    transport)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    route)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    provenance)
                                                                  (truthTotalReflectionDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem truthTotalReflection_round_trip :
    ∀ x : TruthTotalReflectionUp,
      truthTotalReflectionFromEventFlow (truthTotalReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sentenceCodes extensionAttempt diagonal transport route provenance name =>
      change
        some
          (TruthTotalReflectionUp.mk
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist sentenceCodes))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist extensionAttempt))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist diagonal))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist transport))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist route))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist provenance))
            (truthTotalReflectionDecodeBHist (truthTotalReflectionEncodeBHist name))) =
          some
            (TruthTotalReflectionUp.mk sentenceCodes extensionAttempt diagonal transport route
              provenance name)
      rw [truthTotalReflection_decode_encode_bhist sentenceCodes,
        truthTotalReflection_decode_encode_bhist extensionAttempt,
        truthTotalReflection_decode_encode_bhist diagonal,
        truthTotalReflection_decode_encode_bhist transport,
        truthTotalReflection_decode_encode_bhist route,
        truthTotalReflection_decode_encode_bhist provenance,
        truthTotalReflection_decode_encode_bhist name]

private theorem truthTotalReflectionToEventFlow_injective {x y : TruthTotalReflectionUp} :
    truthTotalReflectionToEventFlow x = truthTotalReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      truthTotalReflectionFromEventFlow (truthTotalReflectionToEventFlow x) =
        truthTotalReflectionFromEventFlow (truthTotalReflectionToEventFlow y) :=
    congrArg truthTotalReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (truthTotalReflection_round_trip x).symm
      (Eq.trans hread (truthTotalReflection_round_trip y)))

private def truthTotalReflectionFields :
    TruthTotalReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TruthTotalReflectionUp.mk sentenceCodes extensionAttempt diagonal transport route
      provenance name =>
      [sentenceCodes, extensionAttempt, diagonal, transport, route, provenance, name]

private theorem truthTotalReflection_field_faithful :
    ∀ x y : TruthTotalReflectionUp,
      truthTotalReflectionFields x = truthTotalReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sentenceCodes extensionAttempt diagonal transport route provenance name =>
      cases y with
      | mk sentenceCodes' extensionAttempt' diagonal' transport' route' provenance' name' =>
          cases hfields
          rfl

instance truthTotalReflectionBHistCarrier : BHistCarrier TruthTotalReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := truthTotalReflectionToEventFlow
  fromEventFlow := truthTotalReflectionFromEventFlow

instance truthTotalReflectionChapterTasteGate : ChapterTasteGate TruthTotalReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change truthTotalReflectionFromEventFlow (truthTotalReflectionToEventFlow x) = some x
    exact truthTotalReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (truthTotalReflectionToEventFlow_injective heq)

instance truthTotalReflectionFieldFaithful :
    FieldFaithful TruthTotalReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := truthTotalReflectionFields
  field_faithful := truthTotalReflection_field_faithful

def taste_gate : ChapterTasteGate TruthTotalReflectionUp :=
  truthTotalReflectionChapterTasteGate

theorem TruthTotalReflectionTasteGate_single_carrier_alignment :
    (∀ x : TruthTotalReflectionUp,
      truthTotalReflectionFromEventFlow (truthTotalReflectionToEventFlow x) = some x) ∧
      (∀ x y : TruthTotalReflectionUp,
        truthTotalReflectionToEventFlow x = truthTotalReflectionToEventFlow y → x = y) ∧
        (∀ (x : TruthTotalReflectionUp) w m,
          List.Mem w (truthTotalReflectionToEventFlow x) →
            List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact truthTotalReflection_round_trip
  · constructor
    · intro x y heq
      exact truthTotalReflectionToEventFlow_injective heq
    · intro x w m hw hm
      exact event_flow_conservativity (S := truthTotalReflectionToEventFlow x) hw hm

theorem TruthTotalReflectionUp_taste_gate_boundary :
    (∀ x : TruthTotalReflectionUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : TruthTotalReflectionUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact ⟨truthTotalReflectionToEventFlow x, truthTotalReflection_round_trip x⟩
  · intro x w m hw hm
    exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

theorem TruthTotalReflectionAttemptRowStability (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transports routes provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transports routes provenance
        nameCert ∧
        hsame sentence sentence ∧ hsame attempt attempt ∧ hsame diagonal diagonal ∧
          hsame transports transports ∧ hsame routes routes := by
  -- BEDC touchpoint anchor: BHist hsame
  cases x with
  | mk sentence attempt diagonal transports routes provenance nameCert =>
      exact
        ⟨sentence, attempt, diagonal, transports, routes, provenance, nameCert, rfl,
          hsame_refl sentence, hsame_refl attempt, hsame_refl diagonal,
          hsame_refl transports, hsame_refl routes⟩

end BEDC.Derived.TruthTotalReflectionUp
