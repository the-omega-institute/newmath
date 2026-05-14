import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HashApophaticSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HashApophaticSealUp : Type where
  | mk :
      (digest fiber gap farEnd refusal transport continuation provenance name : BHist) →
      HashApophaticSealUp
  deriving DecidableEq

def hashApophaticSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hashApophaticSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hashApophaticSealEncodeBHist h

def hashApophaticSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hashApophaticSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hashApophaticSealDecodeBHist tail)

private theorem hashApophaticSeal_decode_encode_bhist :
    ∀ h : BHist,
      hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hashApophaticSealToEventFlow : HashApophaticSealUp → EventFlow
  | HashApophaticSealUp.mk digest fiber gap farEnd refusal transport continuation
      provenance name =>
      [[BMark.b0],
        hashApophaticSealEncodeBHist digest,
        [BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist fiber,
        [BMark.b1, BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist farEnd,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hashApophaticSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hashApophaticSealEncodeBHist name]

def hashApophaticSealFromEventFlow : EventFlow → Option HashApophaticSealUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | digest :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | fiber :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | farEnd :: rest7 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (HashApophaticSealUp.mk
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    digest)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    fiber)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    gap)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    farEnd)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    refusal)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    transport)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    continuation)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    provenance)
                                                                                  (hashApophaticSealDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem hashApophaticSeal_round_trip :
    ∀ x : HashApophaticSealUp,
      hashApophaticSealFromEventFlow (hashApophaticSealToEventFlow x) = some x := by
  intro x
  cases x with
  | mk digest fiber gap farEnd refusal transport continuation provenance name =>
      change
        some
          (HashApophaticSealUp.mk
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist digest))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist fiber))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist gap))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist farEnd))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist refusal))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist transport))
            (hashApophaticSealDecodeBHist
              (hashApophaticSealEncodeBHist continuation))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist provenance))
            (hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist name))) =
          some
            (HashApophaticSealUp.mk digest fiber gap farEnd refusal transport
              continuation provenance name)
      rw [hashApophaticSeal_decode_encode_bhist digest,
        hashApophaticSeal_decode_encode_bhist fiber,
        hashApophaticSeal_decode_encode_bhist gap,
        hashApophaticSeal_decode_encode_bhist farEnd,
        hashApophaticSeal_decode_encode_bhist refusal,
        hashApophaticSeal_decode_encode_bhist transport,
        hashApophaticSeal_decode_encode_bhist continuation,
        hashApophaticSeal_decode_encode_bhist provenance,
        hashApophaticSeal_decode_encode_bhist name]

theorem hashApophaticSealToEventFlow_injective
    {x y : HashApophaticSealUp} :
    hashApophaticSealToEventFlow x = hashApophaticSealToEventFlow y → x = y := by
  intro heq
  have hread :
      hashApophaticSealFromEventFlow (hashApophaticSealToEventFlow x) =
        hashApophaticSealFromEventFlow (hashApophaticSealToEventFlow y) :=
    congrArg hashApophaticSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hashApophaticSeal_round_trip x).symm
      (Eq.trans hread (hashApophaticSeal_round_trip y)))

def hashApophaticSealFields : HashApophaticSealUp → List BHist
  | HashApophaticSealUp.mk digest fiber gap farEnd refusal transport continuation
      provenance name =>
      [digest, fiber, gap, farEnd, refusal, transport, continuation, provenance, name]

private theorem hashApophaticSeal_field_faithful :
    ∀ x y : HashApophaticSealUp,
      hashApophaticSealFields x = hashApophaticSealFields y → x = y := by
  intro x y h
  cases x with
  | mk digest₁ fiber₁ gap₁ farEnd₁ refusal₁ transport₁ continuation₁ provenance₁
      name₁ =>
      cases y with
      | mk digest₂ fiber₂ gap₂ farEnd₂ refusal₂ transport₂ continuation₂ provenance₂
          name₂ =>
          cases h
          rfl

instance hashApophaticSealBHistCarrier : BHistCarrier HashApophaticSealUp where
  toEventFlow := hashApophaticSealToEventFlow
  fromEventFlow := hashApophaticSealFromEventFlow

instance hashApophaticSealChapterTasteGate : ChapterTasteGate HashApophaticSealUp where
  round_trip := by
    intro x
    change hashApophaticSealFromEventFlow (hashApophaticSealToEventFlow x) = some x
    exact hashApophaticSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hashApophaticSealToEventFlow_injective heq)

instance hashApophaticSealFieldFaithful : FieldFaithful HashApophaticSealUp where
  fields := hashApophaticSealFields
  field_faithful := hashApophaticSeal_field_faithful

instance hashApophaticSealNontrivial : Nontrivial HashApophaticSealUp where
  witness_pair :=
    ⟨HashApophaticSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HashApophaticSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HashApophaticSealUp :=
  hashApophaticSealChapterTasteGate

theorem HashApophaticSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HashApophaticSealUp) ∧
      Nonempty (FieldFaithful HashApophaticSealUp) ∧
      Nonempty (Nontrivial HashApophaticSealUp) ∧
      (∀ h : BHist,
        hashApophaticSealDecodeBHist (hashApophaticSealEncodeBHist h) = h) ∧
      (∀ x : HashApophaticSealUp,
        hashApophaticSealFromEventFlow (hashApophaticSealToEventFlow x) = some x) ∧
      (∀ x y : HashApophaticSealUp,
        hashApophaticSealToEventFlow x = hashApophaticSealToEventFlow y → x = y) := by
  exact
    ⟨⟨hashApophaticSealChapterTasteGate⟩, ⟨hashApophaticSealFieldFaithful⟩,
      ⟨hashApophaticSealNontrivial⟩, hashApophaticSeal_decode_encode_bhist,
      hashApophaticSeal_round_trip, fun x y heq =>
        hashApophaticSealToEventFlow_injective heq⟩

end BEDC.Derived.HashApophaticSealUp
