import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationReflectionPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationReflectionPacketUp : Type where
  | mk : (S H Sigma C P L E T R N : BHist) → ObservationReflectionPacketUp
  deriving DecidableEq

def observationReflectionPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationReflectionPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationReflectionPacketEncodeBHist h

def observationReflectionPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationReflectionPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationReflectionPacketDecodeBHist tail)

private theorem observationReflectionPacketDecode_encode_bhist :
    ∀ h : BHist,
      observationReflectionPacketDecodeBHist (observationReflectionPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationReflectionPacketToEventFlow : ObservationReflectionPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationReflectionPacketUp.mk S H Sigma C P L E T R N =>
      [[BMark.b0],
        observationReflectionPacketEncodeBHist S,
        [BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist Sigma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationReflectionPacketEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationReflectionPacketEncodeBHist N]

def observationReflectionPacketFromEventFlow : EventFlow → Option ObservationReflectionPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | H :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Sigma :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | L :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | T :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | R :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ObservationReflectionPacketUp.mk
                                                                                          (observationReflectionPacketDecodeBHist S)
                                                                                          (observationReflectionPacketDecodeBHist H)
                                                                                          (observationReflectionPacketDecodeBHist Sigma)
                                                                                          (observationReflectionPacketDecodeBHist C)
                                                                                          (observationReflectionPacketDecodeBHist P)
                                                                                          (observationReflectionPacketDecodeBHist L)
                                                                                          (observationReflectionPacketDecodeBHist E)
                                                                                          (observationReflectionPacketDecodeBHist T)
                                                                                          (observationReflectionPacketDecodeBHist R)
                                                                                          (observationReflectionPacketDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem observationReflectionPacket_round_trip :
    ∀ x : ObservationReflectionPacketUp,
      observationReflectionPacketFromEventFlow (observationReflectionPacketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S H Sigma C P L E T R N =>
      change
        some
          (ObservationReflectionPacketUp.mk
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist S))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist H))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist Sigma))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist C))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist P))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist L))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist E))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist T))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist R))
            (observationReflectionPacketDecodeBHist
              (observationReflectionPacketEncodeBHist N))) =
          some (ObservationReflectionPacketUp.mk S H Sigma C P L E T R N)
      rw [observationReflectionPacketDecode_encode_bhist S,
        observationReflectionPacketDecode_encode_bhist H,
        observationReflectionPacketDecode_encode_bhist Sigma,
        observationReflectionPacketDecode_encode_bhist C,
        observationReflectionPacketDecode_encode_bhist P,
        observationReflectionPacketDecode_encode_bhist L,
        observationReflectionPacketDecode_encode_bhist E,
        observationReflectionPacketDecode_encode_bhist T,
        observationReflectionPacketDecode_encode_bhist R,
        observationReflectionPacketDecode_encode_bhist N]

theorem observationReflectionPacketToEventFlow_injective {x y : ObservationReflectionPacketUp} :
    observationReflectionPacketToEventFlow x = observationReflectionPacketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationReflectionPacketFromEventFlow (observationReflectionPacketToEventFlow x) =
        observationReflectionPacketFromEventFlow (observationReflectionPacketToEventFlow y) :=
    congrArg observationReflectionPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationReflectionPacket_round_trip x).symm
      (Eq.trans hread (observationReflectionPacket_round_trip y)))

instance observationReflectionPacketBHistCarrier : BHistCarrier ObservationReflectionPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationReflectionPacketToEventFlow
  fromEventFlow := observationReflectionPacketFromEventFlow

instance observationReflectionPacketChapterTasteGate :
    ChapterTasteGate ObservationReflectionPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observationReflectionPacketFromEventFlow (observationReflectionPacketToEventFlow x) =
        some x
    exact observationReflectionPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationReflectionPacketToEventFlow_injective heq)

instance observationReflectionPacketFieldFaithful :
    FieldFaithful ObservationReflectionPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObservationReflectionPacketUp.mk S H Sigma C P L E T R N =>
        [S, H, Sigma, C, P, L, E, T, R, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ H₁ Sigma₁ C₁ P₁ L₁ E₁ T₁ R₁ N₁ =>
        cases y with
        | mk S₂ H₂ Sigma₂ C₂ P₂ L₂ E₂ T₂ R₂ N₂ =>
            cases h
            rfl

instance observationReflectionPacketNontrivial : Nontrivial ObservationReflectionPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationReflectionPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationReflectionPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationReflectionPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationReflectionPacketChapterTasteGate

theorem ObservationReflectionPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observationReflectionPacketDecodeBHist (observationReflectionPacketEncodeBHist h) = h) ∧
      (∀ x : ObservationReflectionPacketUp,
        observationReflectionPacketFromEventFlow (observationReflectionPacketToEventFlow x) =
          some x) ∧
        (∀ x y : ObservationReflectionPacketUp,
          observationReflectionPacketToEventFlow x = observationReflectionPacketToEventFlow y →
            x = y) ∧
          observationReflectionPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observationReflectionPacketDecode_encode_bhist
  · constructor
    · exact observationReflectionPacket_round_trip
    · constructor
      · intro x y heq
        exact observationReflectionPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObservationReflectionPacketUp
