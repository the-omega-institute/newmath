import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DigestProvenancePacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DigestProvenancePacketUp : Type where
  | mk (visibleDigest source fiber gap exactness transport replay provenance name : BHist) :
      DigestProvenancePacketUp
  deriving DecidableEq

def digestProvenancePacketEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: digestProvenancePacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: digestProvenancePacketEncodeBHist h

def digestProvenancePacketDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (digestProvenancePacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (digestProvenancePacketDecodeBHist tail)

private theorem digestProvenancePacketDecode_encode_bhist :
    ∀ h : BHist,
      digestProvenancePacketDecodeBHist (digestProvenancePacketEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def digestProvenancePacketToEventFlow : DigestProvenancePacketUp → EventFlow
  | DigestProvenancePacketUp.mk visibleDigest source fiber gap exactness transport replay
      provenance name =>
      [[BMark.b0],
        digestProvenancePacketEncodeBHist visibleDigest,
        [BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist fiber,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist exactness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        digestProvenancePacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        digestProvenancePacketEncodeBHist name]

def digestProvenancePacketFromEventFlow :
    EventFlow → Option DigestProvenancePacketUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | visibleDigest :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | source :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fiber :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gap :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | exactness :: rest9 =>
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
                                                      | replay :: rest13 =>
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
                                                                                (DigestProvenancePacketUp.mk
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    visibleDigest)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    source)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    fiber)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    gap)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    exactness)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    transport)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    replay)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    provenance)
                                                                                  (digestProvenancePacketDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem digestProvenancePacket_round_trip :
    ∀ x : DigestProvenancePacketUp,
      digestProvenancePacketFromEventFlow
        (digestProvenancePacketToEventFlow x) = some x := by
  intro x
  cases x with
  | mk visibleDigest source fiber gap exactness transport replay provenance name =>
      change
        some
          (DigestProvenancePacketUp.mk
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist visibleDigest))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist source))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist fiber))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist gap))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist exactness))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist transport))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist replay))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist provenance))
            (digestProvenancePacketDecodeBHist
              (digestProvenancePacketEncodeBHist name))) =
          some
            (DigestProvenancePacketUp.mk visibleDigest source fiber gap exactness transport
              replay provenance name)
      rw [digestProvenancePacketDecode_encode_bhist visibleDigest,
        digestProvenancePacketDecode_encode_bhist source,
        digestProvenancePacketDecode_encode_bhist fiber,
        digestProvenancePacketDecode_encode_bhist gap,
        digestProvenancePacketDecode_encode_bhist exactness,
        digestProvenancePacketDecode_encode_bhist transport,
        digestProvenancePacketDecode_encode_bhist replay,
        digestProvenancePacketDecode_encode_bhist provenance,
        digestProvenancePacketDecode_encode_bhist name]

theorem digestProvenancePacketToEventFlow_injective
    {x y : DigestProvenancePacketUp} :
    digestProvenancePacketToEventFlow x = digestProvenancePacketToEventFlow y → x = y := by
  intro heq
  have hread :
      digestProvenancePacketFromEventFlow (digestProvenancePacketToEventFlow x) =
        digestProvenancePacketFromEventFlow (digestProvenancePacketToEventFlow y) :=
    congrArg digestProvenancePacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (digestProvenancePacket_round_trip x).symm
      (Eq.trans hread (digestProvenancePacket_round_trip y)))

instance digestProvenancePacketBHistCarrier :
    BHistCarrier DigestProvenancePacketUp where
  toEventFlow := digestProvenancePacketToEventFlow
  fromEventFlow := digestProvenancePacketFromEventFlow

instance digestProvenancePacketChapterTasteGate :
    ChapterTasteGate DigestProvenancePacketUp where
  round_trip := by
    intro x
    change digestProvenancePacketFromEventFlow (digestProvenancePacketToEventFlow x) =
      some x
    exact digestProvenancePacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (digestProvenancePacketToEventFlow_injective heq)

instance digestProvenancePacketFieldFaithful :
    FieldFaithful DigestProvenancePacketUp where
  fields := fun x =>
    match x with
    | DigestProvenancePacketUp.mk visibleDigest source fiber gap exactness transport replay
        provenance name =>
        [visibleDigest, source, fiber, gap, exactness, transport, replay, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk visibleDigest₁ source₁ fiber₁ gap₁ exactness₁ transport₁ replay₁ provenance₁
        name₁ =>
        cases y with
        | mk visibleDigest₂ source₂ fiber₂ gap₂ exactness₂ transport₂ replay₂ provenance₂
            name₂ =>
            cases h
            rfl

instance digestProvenancePacketNontrivial : Nontrivial DigestProvenancePacketUp where
  witness_pair :=
    ⟨DigestProvenancePacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DigestProvenancePacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem taste_gate :
    Nonempty (ChapterTasteGate DigestProvenancePacketUp) ∧
      Nonempty (FieldFaithful DigestProvenancePacketUp) ∧
        Nonempty (Nontrivial DigestProvenancePacketUp) := by
  constructor
  · exact ⟨digestProvenancePacketChapterTasteGate⟩
  · constructor
    · exact ⟨digestProvenancePacketFieldFaithful⟩
    · exact ⟨digestProvenancePacketNontrivial⟩

theorem DigestProvenancePacketTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DigestProvenancePacketUp) ∧
      Nonempty (FieldFaithful DigestProvenancePacketUp) ∧
        Nonempty (Nontrivial DigestProvenancePacketUp) ∧
          (∀ x : DigestProvenancePacketUp,
            digestProvenancePacketFromEventFlow (digestProvenancePacketToEventFlow x) =
              some x) ∧
            (∀ x y : DigestProvenancePacketUp,
              digestProvenancePacketToEventFlow x =
                digestProvenancePacketToEventFlow y → x = y) ∧
              digestProvenancePacketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  constructor
  · exact ⟨digestProvenancePacketChapterTasteGate⟩
  · constructor
    · exact ⟨digestProvenancePacketFieldFaithful⟩
    · constructor
      · exact ⟨digestProvenancePacketNontrivial⟩
      · constructor
        · exact digestProvenancePacket_round_trip
        · constructor
          · intro x y heq
            exact digestProvenancePacketToEventFlow_injective heq
          · rfl

end BEDC.Derived.DigestProvenancePacketUp
