import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationReflectionHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationReflectionHandoffUp : Type where
  | mk (observation streamName realBudget selector limiter kernelSieve classifier transport
      memory externalRead provenance nameCert : BHist) : ObservationReflectionHandoffUp
  deriving DecidableEq

def observationReflectionHandoffEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationReflectionHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationReflectionHandoffEncodeBHist h

def observationReflectionHandoffDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationReflectionHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationReflectionHandoffDecodeBHist tail)

private theorem observationReflectionHandoff_decode_encode_bhist :
    ∀ h : BHist,
      observationReflectionHandoffDecodeBHist
        (observationReflectionHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationReflectionHandoffFields :
    ObservationReflectionHandoffUp → List BHist
  | ObservationReflectionHandoffUp.mk observation streamName realBudget selector limiter
      kernelSieve classifier transport memory externalRead provenance nameCert =>
      [observation, streamName, realBudget, selector, limiter, kernelSieve, classifier,
        transport, memory, externalRead, provenance, nameCert]

def observationReflectionHandoffToEventFlow :
    ObservationReflectionHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationReflectionHandoffUp.mk observation streamName realBudget selector limiter
      kernelSieve classifier transport memory externalRead provenance nameCert =>
      [observationReflectionHandoffEncodeBHist observation,
        observationReflectionHandoffEncodeBHist streamName,
        observationReflectionHandoffEncodeBHist realBudget,
        observationReflectionHandoffEncodeBHist selector,
        observationReflectionHandoffEncodeBHist limiter,
        observationReflectionHandoffEncodeBHist kernelSieve,
        observationReflectionHandoffEncodeBHist classifier,
        observationReflectionHandoffEncodeBHist transport,
        observationReflectionHandoffEncodeBHist memory,
        observationReflectionHandoffEncodeBHist externalRead,
        observationReflectionHandoffEncodeBHist provenance,
        observationReflectionHandoffEncodeBHist nameCert]

def observationReflectionHandoffFromEventFlow :
    EventFlow → Option ObservationReflectionHandoffUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observation :: rest0 =>
      match rest0 with
      | [] => none
      | streamName :: rest1 =>
          match rest1 with
          | [] => none
          | realBudget :: rest2 =>
              match rest2 with
              | [] => none
              | selector :: rest3 =>
                  match rest3 with
                  | [] => none
                  | limiter :: rest4 =>
                      match rest4 with
                      | [] => none
                      | kernelSieve :: rest5 =>
                          match rest5 with
                          | [] => none
                          | classifier :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | memory :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | externalRead :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameCert :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ObservationReflectionHandoffUp.mk
                                                          (observationReflectionHandoffDecodeBHist
                                                            observation)
                                                          (observationReflectionHandoffDecodeBHist
                                                            streamName)
                                                          (observationReflectionHandoffDecodeBHist
                                                            realBudget)
                                                          (observationReflectionHandoffDecodeBHist
                                                            selector)
                                                          (observationReflectionHandoffDecodeBHist
                                                            limiter)
                                                          (observationReflectionHandoffDecodeBHist
                                                            kernelSieve)
                                                          (observationReflectionHandoffDecodeBHist
                                                            classifier)
                                                          (observationReflectionHandoffDecodeBHist
                                                            transport)
                                                          (observationReflectionHandoffDecodeBHist
                                                            memory)
                                                          (observationReflectionHandoffDecodeBHist
                                                            externalRead)
                                                          (observationReflectionHandoffDecodeBHist
                                                            provenance)
                                                          (observationReflectionHandoffDecodeBHist
                                                            nameCert))
                                                  | _ :: _ => none

private theorem observationReflectionHandoff_round_trip :
    ∀ x : ObservationReflectionHandoffUp,
      observationReflectionHandoffFromEventFlow
        (observationReflectionHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observation streamName realBudget selector limiter kernelSieve classifier transport
      memory externalRead provenance nameCert =>
      change
        some
          (ObservationReflectionHandoffUp.mk
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist observation))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist streamName))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist realBudget))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist selector))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist limiter))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist kernelSieve))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist classifier))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist transport))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist memory))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist externalRead))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist provenance))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist nameCert))) =
          some
            (ObservationReflectionHandoffUp.mk observation streamName realBudget selector
              limiter kernelSieve classifier transport memory externalRead provenance nameCert)
      rw [observationReflectionHandoff_decode_encode_bhist observation,
        observationReflectionHandoff_decode_encode_bhist streamName,
        observationReflectionHandoff_decode_encode_bhist realBudget,
        observationReflectionHandoff_decode_encode_bhist selector,
        observationReflectionHandoff_decode_encode_bhist limiter,
        observationReflectionHandoff_decode_encode_bhist kernelSieve,
        observationReflectionHandoff_decode_encode_bhist classifier,
        observationReflectionHandoff_decode_encode_bhist transport,
        observationReflectionHandoff_decode_encode_bhist memory,
        observationReflectionHandoff_decode_encode_bhist externalRead,
        observationReflectionHandoff_decode_encode_bhist provenance,
        observationReflectionHandoff_decode_encode_bhist nameCert]

private theorem observationReflectionHandoffToEventFlow_injective
    {x y : ObservationReflectionHandoffUp} :
    observationReflectionHandoffToEventFlow x = observationReflectionHandoffToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationReflectionHandoffFromEventFlow (observationReflectionHandoffToEventFlow x) =
        observationReflectionHandoffFromEventFlow (observationReflectionHandoffToEventFlow y) :=
    congrArg observationReflectionHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationReflectionHandoff_round_trip x).symm
      (Eq.trans hread (observationReflectionHandoff_round_trip y)))

private theorem observationReflectionHandoff_field_faithful :
    ∀ x y : ObservationReflectionHandoffUp,
      observationReflectionHandoffFields x = observationReflectionHandoffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observation streamName realBudget selector limiter kernelSieve classifier transport
      memory externalRead provenance nameCert =>
      cases y with
      | mk observation' streamName' realBudget' selector' limiter' kernelSieve' classifier'
          transport' memory' externalRead' provenance' nameCert' =>
          cases hfields
          rfl

instance observationReflectionHandoffBHistCarrier :
    BHistCarrier ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationReflectionHandoffToEventFlow
  fromEventFlow := observationReflectionHandoffFromEventFlow

instance observationReflectionHandoffChapterTasteGate :
    ChapterTasteGate ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observationReflectionHandoffFromEventFlow
        (observationReflectionHandoffToEventFlow x) = some x
    exact observationReflectionHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationReflectionHandoffToEventFlow_injective heq)

instance observationReflectionHandoffFieldFaithful :
    FieldFaithful ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationReflectionHandoffFields
  field_faithful := observationReflectionHandoff_field_faithful

instance observationReflectionHandoffNontrivial :
    Nontrivial ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationReflectionHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ObservationReflectionHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationReflectionHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationReflectionHandoffChapterTasteGate

theorem ObservationReflectionHandoffUp_taste_gate_boundary :
    (∀ x : ObservationReflectionHandoffUp,
      ∃ e : EventFlow, observationReflectionHandoffFromEventFlow e = some x) ∧
      (∀ (x : ObservationReflectionHandoffUp) (w : RawEvent) (m : BMark),
        List.Mem w (observationReflectionHandoffToEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · intro x
    exact ⟨observationReflectionHandoffToEventFlow x, observationReflectionHandoff_round_trip x⟩
  · intro _x _w m _hw _hm
    cases m with
    | b0 => exact Or.inl rfl
    | b1 => exact Or.inr rfl

theorem ObservationReflectionHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observationReflectionHandoffDecodeBHist (observationReflectionHandoffEncodeBHist h) =
        h) ∧
      (∀ x : ObservationReflectionHandoffUp,
        observationReflectionHandoffFromEventFlow (observationReflectionHandoffToEventFlow x) =
          some x) ∧
        (∀ x y : ObservationReflectionHandoffUp,
          observationReflectionHandoffToEventFlow x = observationReflectionHandoffToEventFlow y ->
            x = y) ∧
          observationReflectionHandoffEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : ObservationReflectionHandoffUp,
              observationReflectionHandoffFields x = observationReflectionHandoffFields y ->
                x = y) ∧
              (∃ x y : ObservationReflectionHandoffUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨observationReflectionHandoff_decode_encode_bhist,
      observationReflectionHandoff_round_trip,
      fun _x _y heq => observationReflectionHandoffToEventFlow_injective heq,
      rfl,
      observationReflectionHandoff_field_faithful,
      ⟨ObservationReflectionHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        ObservationReflectionHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.ObservationReflectionHandoffUp
