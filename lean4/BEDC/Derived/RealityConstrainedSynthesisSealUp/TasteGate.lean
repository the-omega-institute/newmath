import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSynthesisSealUp : Type where
  | mk : (audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name : BHist) → RealityConstrainedSynthesisSealUp
  deriving DecidableEq

def realityConstrainedSynthesisSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSynthesisSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSynthesisSealEncodeBHist h

def realityConstrainedSynthesisSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSynthesisSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSynthesisSealDecodeBHist tail)

private theorem realityConstrainedSynthesisSeal_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realityConstrainedSynthesisSealFields :
    RealityConstrainedSynthesisSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSynthesisSealUp.mk audit fit objectivity observation explanation tower
      ledger failure transport replay provenance name =>
      [audit, fit, objectivity, observation, explanation, tower, ledger, failure, transport,
        replay, provenance, name]

def realityConstrainedSynthesisSealToEventFlow :
    RealityConstrainedSynthesisSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realityConstrainedSynthesisSealFields x).map
        realityConstrainedSynthesisSealEncodeBHist

private def realityConstrainedSynthesisSealDecodePacket
    (audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name : RawEvent) : RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealityConstrainedSynthesisSealUp.mk
    (realityConstrainedSynthesisSealDecodeBHist audit)
    (realityConstrainedSynthesisSealDecodeBHist fit)
    (realityConstrainedSynthesisSealDecodeBHist objectivity)
    (realityConstrainedSynthesisSealDecodeBHist observation)
    (realityConstrainedSynthesisSealDecodeBHist explanation)
    (realityConstrainedSynthesisSealDecodeBHist tower)
    (realityConstrainedSynthesisSealDecodeBHist ledger)
    (realityConstrainedSynthesisSealDecodeBHist failure)
    (realityConstrainedSynthesisSealDecodeBHist transport)
    (realityConstrainedSynthesisSealDecodeBHist replay)
    (realityConstrainedSynthesisSealDecodeBHist provenance)
    (realityConstrainedSynthesisSealDecodeBHist name)

private def realityConstrainedSynthesisSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => realityConstrainedSynthesisSealRawAt n rest

private def realityConstrainedSynthesisSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => realityConstrainedSynthesisSealLengthEq n rest

def realityConstrainedSynthesisSealFromEventFlow :
    EventFlow → Option RealityConstrainedSynthesisSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match realityConstrainedSynthesisSealLengthEq 12 flow with
      | true =>
          some
            (realityConstrainedSynthesisSealDecodePacket
              (realityConstrainedSynthesisSealRawAt 0 flow)
              (realityConstrainedSynthesisSealRawAt 1 flow)
              (realityConstrainedSynthesisSealRawAt 2 flow)
              (realityConstrainedSynthesisSealRawAt 3 flow)
              (realityConstrainedSynthesisSealRawAt 4 flow)
              (realityConstrainedSynthesisSealRawAt 5 flow)
              (realityConstrainedSynthesisSealRawAt 6 flow)
              (realityConstrainedSynthesisSealRawAt 7 flow)
              (realityConstrainedSynthesisSealRawAt 8 flow)
              (realityConstrainedSynthesisSealRawAt 9 flow)
              (realityConstrainedSynthesisSealRawAt 10 flow)
              (realityConstrainedSynthesisSealRawAt 11 flow))
      | false => none

private theorem realityConstrainedSynthesisSeal_round_trip :
    ∀ x : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name =>
      change
        some
          (realityConstrainedSynthesisSealDecodePacket
            (realityConstrainedSynthesisSealEncodeBHist audit)
            (realityConstrainedSynthesisSealEncodeBHist fit)
            (realityConstrainedSynthesisSealEncodeBHist objectivity)
            (realityConstrainedSynthesisSealEncodeBHist observation)
            (realityConstrainedSynthesisSealEncodeBHist explanation)
            (realityConstrainedSynthesisSealEncodeBHist tower)
            (realityConstrainedSynthesisSealEncodeBHist ledger)
            (realityConstrainedSynthesisSealEncodeBHist failure)
            (realityConstrainedSynthesisSealEncodeBHist transport)
            (realityConstrainedSynthesisSealEncodeBHist replay)
            (realityConstrainedSynthesisSealEncodeBHist provenance)
            (realityConstrainedSynthesisSealEncodeBHist name)) =
          some
            (RealityConstrainedSynthesisSealUp.mk audit fit objectivity observation
              explanation tower ledger failure transport replay provenance name)
      unfold realityConstrainedSynthesisSealDecodePacket
      rw [realityConstrainedSynthesisSeal_decode_encode_bhist audit,
        realityConstrainedSynthesisSeal_decode_encode_bhist fit,
        realityConstrainedSynthesisSeal_decode_encode_bhist objectivity,
        realityConstrainedSynthesisSeal_decode_encode_bhist observation,
        realityConstrainedSynthesisSeal_decode_encode_bhist explanation,
        realityConstrainedSynthesisSeal_decode_encode_bhist tower,
        realityConstrainedSynthesisSeal_decode_encode_bhist ledger,
        realityConstrainedSynthesisSeal_decode_encode_bhist failure,
        realityConstrainedSynthesisSeal_decode_encode_bhist transport,
        realityConstrainedSynthesisSeal_decode_encode_bhist replay,
        realityConstrainedSynthesisSeal_decode_encode_bhist provenance,
        realityConstrainedSynthesisSeal_decode_encode_bhist name]

private theorem realityConstrainedSynthesisSealToEventFlow_injective
    {x y : RealityConstrainedSynthesisSealUp} :
    realityConstrainedSynthesisSealToEventFlow x =
      realityConstrainedSynthesisSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow x) =
        realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow y) :=
    congrArg realityConstrainedSynthesisSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSynthesisSeal_round_trip x).symm
      (Eq.trans hread (realityConstrainedSynthesisSeal_round_trip y)))

private theorem realityConstrainedSynthesisSeal_fields_faithful :
    ∀ x y : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFields x =
        realityConstrainedSynthesisSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk audit₁ fit₁ objectivity₁ observation₁ explanation₁ tower₁ ledger₁ failure₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk audit₂ fit₂ objectivity₂ observation₂ explanation₂ tower₂ ledger₂ failure₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance realityConstrainedSynthesisSealBHistCarrier :
    BHistCarrier RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSynthesisSealToEventFlow
  fromEventFlow := realityConstrainedSynthesisSealFromEventFlow

instance realityConstrainedSynthesisSealChapterTasteGate :
    ChapterTasteGate RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x
    exact realityConstrainedSynthesisSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSynthesisSealToEventFlow_injective heq)

instance realityConstrainedSynthesisSealFieldFaithful :
    FieldFaithful RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSynthesisSealFields
  field_faithful := realityConstrainedSynthesisSeal_fields_faithful

instance realityConstrainedSynthesisSealNontrivial :
    Nontrivial RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSynthesisSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSynthesisSealUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSynthesisSealChapterTasteGate

theorem RealityConstrainedSynthesisSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedSynthesisSealUp,
        realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedSynthesisSealUp,
          realityConstrainedSynthesisSealToEventFlow x =
            realityConstrainedSynthesisSealToEventFlow y → x = y) ∧
          realityConstrainedSynthesisSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨realityConstrainedSynthesisSeal_decode_encode_bhist,
      realityConstrainedSynthesisSeal_round_trip,
      (fun _ _ heq => realityConstrainedSynthesisSealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealityConstrainedSynthesisSealUp
