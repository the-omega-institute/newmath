import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealWindowClassifierSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealWindowClassifierSealUp : Type where
  | mk :
      (stream dyadic regular realSeal classifier refusal transport replay provenance name : BHist) →
      RealWindowClassifierSealUp
  deriving DecidableEq

def realWindowClassifierSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realWindowClassifierSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realWindowClassifierSealEncodeBHist h

def realWindowClassifierSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realWindowClassifierSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realWindowClassifierSealDecodeBHist tail)

private theorem realWindowClassifierSeal_decode_encode_bhist :
    ∀ h : BHist,
      realWindowClassifierSealDecodeBHist (realWindowClassifierSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realWindowClassifierSealToEventFlow : RealWindowClassifierSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealWindowClassifierSealUp.mk stream dyadic regular realSeal classifier refusal transport replay
      provenance name =>
      [[BMark.b0],
        realWindowClassifierSealEncodeBHist stream,
        [BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realWindowClassifierSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realWindowClassifierSealEncodeBHist name]

def realWindowClassifierSealFromEventFlow : EventFlow → Option RealWindowClassifierSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, stream, _tag1, dyadic, _tag2, regular, _tag3, realSeal, _tag4, classifier,
      _tag5, refusal, _tag6, transport, _tag7, replay, _tag8, provenance, _tag9, name] =>
      some
        (RealWindowClassifierSealUp.mk
          (realWindowClassifierSealDecodeBHist stream)
          (realWindowClassifierSealDecodeBHist dyadic)
          (realWindowClassifierSealDecodeBHist regular)
          (realWindowClassifierSealDecodeBHist realSeal)
          (realWindowClassifierSealDecodeBHist classifier)
          (realWindowClassifierSealDecodeBHist refusal)
          (realWindowClassifierSealDecodeBHist transport)
          (realWindowClassifierSealDecodeBHist replay)
          (realWindowClassifierSealDecodeBHist provenance)
          (realWindowClassifierSealDecodeBHist name))
  | _ => none

private theorem realWindowClassifierSeal_round_trip :
    ∀ x : RealWindowClassifierSealUp,
      realWindowClassifierSealFromEventFlow (realWindowClassifierSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream dyadic regular realSeal classifier refusal transport replay provenance name =>
      change
        some
          (RealWindowClassifierSealUp.mk
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist stream))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist dyadic))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist regular))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist realSeal))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist classifier))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist refusal))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist transport))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist replay))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist provenance))
            (realWindowClassifierSealDecodeBHist
              (realWindowClassifierSealEncodeBHist name))) =
          some
            (RealWindowClassifierSealUp.mk stream dyadic regular realSeal classifier refusal
              transport replay provenance name)
      rw [realWindowClassifierSeal_decode_encode_bhist stream,
        realWindowClassifierSeal_decode_encode_bhist dyadic,
        realWindowClassifierSeal_decode_encode_bhist regular,
        realWindowClassifierSeal_decode_encode_bhist realSeal,
        realWindowClassifierSeal_decode_encode_bhist classifier,
        realWindowClassifierSeal_decode_encode_bhist refusal,
        realWindowClassifierSeal_decode_encode_bhist transport,
        realWindowClassifierSeal_decode_encode_bhist replay,
        realWindowClassifierSeal_decode_encode_bhist provenance,
        realWindowClassifierSeal_decode_encode_bhist name]

private theorem realWindowClassifierSealToEventFlow_injective
    {x y : RealWindowClassifierSealUp} :
    realWindowClassifierSealToEventFlow x = realWindowClassifierSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realWindowClassifierSealFromEventFlow (realWindowClassifierSealToEventFlow x) =
        realWindowClassifierSealFromEventFlow (realWindowClassifierSealToEventFlow y) :=
    congrArg realWindowClassifierSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realWindowClassifierSeal_round_trip x).symm
      (Eq.trans hread (realWindowClassifierSeal_round_trip y)))

private def realWindowClassifierSealFields : RealWindowClassifierSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealWindowClassifierSealUp.mk stream dyadic regular realSeal classifier refusal transport replay
      provenance name =>
      [stream, dyadic, regular, realSeal, classifier, refusal, transport, replay, provenance,
        name]

private theorem realWindowClassifierSeal_field_faithful :
    ∀ x y : RealWindowClassifierSealUp,
      realWindowClassifierSealFields x = realWindowClassifierSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream₁ dyadic₁ regular₁ realSeal₁ classifier₁ refusal₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk stream₂ dyadic₂ regular₂ realSeal₂ classifier₂ refusal₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance realWindowClassifierSealBHistCarrier : BHistCarrier RealWindowClassifierSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realWindowClassifierSealToEventFlow
  fromEventFlow := realWindowClassifierSealFromEventFlow

instance realWindowClassifierSealChapterTasteGate :
    ChapterTasteGate RealWindowClassifierSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realWindowClassifierSealFromEventFlow (realWindowClassifierSealToEventFlow x) =
        some x
    exact realWindowClassifierSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realWindowClassifierSealToEventFlow_injective heq)

instance realWindowClassifierSealFieldFaithful : FieldFaithful RealWindowClassifierSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realWindowClassifierSealFields
  field_faithful := realWindowClassifierSeal_field_faithful

instance realWindowClassifierSealNontrivial : Nontrivial RealWindowClassifierSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealWindowClassifierSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealWindowClassifierSealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealWindowClassifierSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realWindowClassifierSealChapterTasteGate

end BEDC.Derived.RealWindowClassifierSealUp
