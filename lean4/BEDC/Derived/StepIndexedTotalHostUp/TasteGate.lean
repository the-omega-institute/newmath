import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StepIndexedTotalHostUp : Type where
  | mk : (host fuel trace normal bounded refusal transport route provenance name : BHist) →
      StepIndexedTotalHostUp
  deriving DecidableEq

def stepIndexedTotalHostEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stepIndexedTotalHostEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stepIndexedTotalHostEncodeBHist h

def stepIndexedTotalHostDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stepIndexedTotalHostDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stepIndexedTotalHostDecodeBHist tail)

private theorem stepIndexedTotalHost_decode_encode_bhist :
    ∀ h : BHist,
      stepIndexedTotalHostDecodeBHist (stepIndexedTotalHostEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stepIndexedTotalHostFields : StepIndexedTotalHostUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StepIndexedTotalHostUp.mk host fuel trace normal bounded refusal transport route
      provenance name =>
      [host, fuel, trace, normal, bounded, refusal, transport, route, provenance, name]

def stepIndexedTotalHostToEventFlow : StepIndexedTotalHostUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stepIndexedTotalHostFields x).map stepIndexedTotalHostEncodeBHist

private def stepIndexedTotalHostDecodePacket
    (host fuel trace normal bounded refusal transport route provenance name : RawEvent) :
    StepIndexedTotalHostUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StepIndexedTotalHostUp.mk
    (stepIndexedTotalHostDecodeBHist host)
    (stepIndexedTotalHostDecodeBHist fuel)
    (stepIndexedTotalHostDecodeBHist trace)
    (stepIndexedTotalHostDecodeBHist normal)
    (stepIndexedTotalHostDecodeBHist bounded)
    (stepIndexedTotalHostDecodeBHist refusal)
    (stepIndexedTotalHostDecodeBHist transport)
    (stepIndexedTotalHostDecodeBHist route)
    (stepIndexedTotalHostDecodeBHist provenance)
    (stepIndexedTotalHostDecodeBHist name)

private def stepIndexedTotalHostRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => stepIndexedTotalHostRawAt n rest

private def stepIndexedTotalHostLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => stepIndexedTotalHostLengthEq n rest

def stepIndexedTotalHostFromEventFlow : EventFlow → Option StepIndexedTotalHostUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match stepIndexedTotalHostLengthEq 10 flow with
      | true =>
          some
            (stepIndexedTotalHostDecodePacket
              (stepIndexedTotalHostRawAt 0 flow)
              (stepIndexedTotalHostRawAt 1 flow)
              (stepIndexedTotalHostRawAt 2 flow)
              (stepIndexedTotalHostRawAt 3 flow)
              (stepIndexedTotalHostRawAt 4 flow)
              (stepIndexedTotalHostRawAt 5 flow)
              (stepIndexedTotalHostRawAt 6 flow)
              (stepIndexedTotalHostRawAt 7 flow)
              (stepIndexedTotalHostRawAt 8 flow)
              (stepIndexedTotalHostRawAt 9 flow))
      | false => none

private theorem stepIndexedTotalHost_round_trip :
    ∀ x : StepIndexedTotalHostUp,
      stepIndexedTotalHostFromEventFlow
        (stepIndexedTotalHostToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk host fuel trace normal bounded refusal transport route provenance name =>
      change
        some
          (stepIndexedTotalHostDecodePacket
            (stepIndexedTotalHostEncodeBHist host)
            (stepIndexedTotalHostEncodeBHist fuel)
            (stepIndexedTotalHostEncodeBHist trace)
            (stepIndexedTotalHostEncodeBHist normal)
            (stepIndexedTotalHostEncodeBHist bounded)
            (stepIndexedTotalHostEncodeBHist refusal)
            (stepIndexedTotalHostEncodeBHist transport)
            (stepIndexedTotalHostEncodeBHist route)
            (stepIndexedTotalHostEncodeBHist provenance)
            (stepIndexedTotalHostEncodeBHist name)) =
          some
            (StepIndexedTotalHostUp.mk host fuel trace normal bounded refusal transport
              route provenance name)
      unfold stepIndexedTotalHostDecodePacket
      rw [stepIndexedTotalHost_decode_encode_bhist host,
        stepIndexedTotalHost_decode_encode_bhist fuel,
        stepIndexedTotalHost_decode_encode_bhist trace,
        stepIndexedTotalHost_decode_encode_bhist normal,
        stepIndexedTotalHost_decode_encode_bhist bounded,
        stepIndexedTotalHost_decode_encode_bhist refusal,
        stepIndexedTotalHost_decode_encode_bhist transport,
        stepIndexedTotalHost_decode_encode_bhist route,
        stepIndexedTotalHost_decode_encode_bhist provenance,
        stepIndexedTotalHost_decode_encode_bhist name]

private theorem stepIndexedTotalHostToEventFlow_injective
    {x y : StepIndexedTotalHostUp} :
    stepIndexedTotalHostToEventFlow x =
      stepIndexedTotalHostToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stepIndexedTotalHostFromEventFlow
          (stepIndexedTotalHostToEventFlow x) =
        stepIndexedTotalHostFromEventFlow
          (stepIndexedTotalHostToEventFlow y) :=
    congrArg stepIndexedTotalHostFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stepIndexedTotalHost_round_trip x).symm
      (Eq.trans hread (stepIndexedTotalHost_round_trip y)))

private theorem stepIndexedTotalHost_fields_faithful :
    ∀ x y : StepIndexedTotalHostUp,
      stepIndexedTotalHostFields x = stepIndexedTotalHostFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk host₁ fuel₁ trace₁ normal₁ bounded₁ refusal₁ transport₁ route₁ provenance₁
      name₁ =>
      cases y with
      | mk host₂ fuel₂ trace₂ normal₂ bounded₂ refusal₂ transport₂ route₂ provenance₂
          name₂ =>
          cases hfields
          rfl

instance stepIndexedTotalHostBHistCarrier :
    BHistCarrier StepIndexedTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stepIndexedTotalHostToEventFlow
  fromEventFlow := stepIndexedTotalHostFromEventFlow

instance stepIndexedTotalHostChapterTasteGate :
    ChapterTasteGate StepIndexedTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stepIndexedTotalHostFromEventFlow
        (stepIndexedTotalHostToEventFlow x) = some x
    exact stepIndexedTotalHost_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stepIndexedTotalHostToEventFlow_injective heq)

instance stepIndexedTotalHostFieldFaithful :
    FieldFaithful StepIndexedTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stepIndexedTotalHostFields
  field_faithful := stepIndexedTotalHost_fields_faithful

instance stepIndexedTotalHostNontrivial :
    Nontrivial StepIndexedTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StepIndexedTotalHostUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StepIndexedTotalHostUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StepIndexedTotalHostUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stepIndexedTotalHostChapterTasteGate

theorem StepIndexedTotalHostTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StepIndexedTotalHostUp) ∧
      Nonempty (FieldFaithful StepIndexedTotalHostUp) ∧
        Nonempty (Nontrivial StepIndexedTotalHostUp) ∧
          (∀ h : BHist,
            stepIndexedTotalHostDecodeBHist
              (stepIndexedTotalHostEncodeBHist h) = h) ∧
            (∀ x : StepIndexedTotalHostUp,
              stepIndexedTotalHostFromEventFlow
                (stepIndexedTotalHostToEventFlow x) = some x) ∧
              (∀ x y : StepIndexedTotalHostUp,
                stepIndexedTotalHostToEventFlow x =
                    stepIndexedTotalHostToEventFlow y →
                  x = y) ∧
                stepIndexedTotalHostEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨stepIndexedTotalHostChapterTasteGate⟩,
      ⟨stepIndexedTotalHostFieldFaithful⟩,
      ⟨stepIndexedTotalHostNontrivial⟩,
      stepIndexedTotalHost_decode_encode_bhist,
      stepIndexedTotalHost_round_trip,
      (fun _ _ heq => stepIndexedTotalHostToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StepIndexedTotalHostUp
