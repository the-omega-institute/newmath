import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FuelBoundedPartialTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FuelBoundedPartialTraceUp : Type where
  | mk : (fuel substrate initial trace readback refusal transport route provenance name : BHist) →
      FuelBoundedPartialTraceUp
  deriving DecidableEq

def fuelBoundedPartialTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fuelBoundedPartialTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fuelBoundedPartialTraceEncodeBHist h

def fuelBoundedPartialTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fuelBoundedPartialTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fuelBoundedPartialTraceDecodeBHist tail)

private theorem fuelBoundedPartialTrace_decode_encode_bhist :
    ∀ h : BHist,
      fuelBoundedPartialTraceDecodeBHist (fuelBoundedPartialTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fuelBoundedPartialTraceFields : FuelBoundedPartialTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FuelBoundedPartialTraceUp.mk fuel substrate initial trace readback refusal transport route
      provenance name =>
      [fuel, substrate, initial, trace, readback, refusal, transport, route, provenance, name]

def fuelBoundedPartialTraceToEventFlow : FuelBoundedPartialTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fuelBoundedPartialTraceFields x).map fuelBoundedPartialTraceEncodeBHist

private def fuelBoundedPartialTraceDecodePacket
    (fuel substrate initial trace readback refusal transport route provenance name : RawEvent) :
    FuelBoundedPartialTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FuelBoundedPartialTraceUp.mk
    (fuelBoundedPartialTraceDecodeBHist fuel)
    (fuelBoundedPartialTraceDecodeBHist substrate)
    (fuelBoundedPartialTraceDecodeBHist initial)
    (fuelBoundedPartialTraceDecodeBHist trace)
    (fuelBoundedPartialTraceDecodeBHist readback)
    (fuelBoundedPartialTraceDecodeBHist refusal)
    (fuelBoundedPartialTraceDecodeBHist transport)
    (fuelBoundedPartialTraceDecodeBHist route)
    (fuelBoundedPartialTraceDecodeBHist provenance)
    (fuelBoundedPartialTraceDecodeBHist name)

private def fuelBoundedPartialTraceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fuelBoundedPartialTraceRawAt n rest

private def fuelBoundedPartialTraceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fuelBoundedPartialTraceLengthEq n rest

def fuelBoundedPartialTraceFromEventFlow : EventFlow → Option FuelBoundedPartialTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match fuelBoundedPartialTraceLengthEq 10 flow with
      | true =>
          some
            (fuelBoundedPartialTraceDecodePacket
              (fuelBoundedPartialTraceRawAt 0 flow)
              (fuelBoundedPartialTraceRawAt 1 flow)
              (fuelBoundedPartialTraceRawAt 2 flow)
              (fuelBoundedPartialTraceRawAt 3 flow)
              (fuelBoundedPartialTraceRawAt 4 flow)
              (fuelBoundedPartialTraceRawAt 5 flow)
              (fuelBoundedPartialTraceRawAt 6 flow)
              (fuelBoundedPartialTraceRawAt 7 flow)
              (fuelBoundedPartialTraceRawAt 8 flow)
              (fuelBoundedPartialTraceRawAt 9 flow))
      | false => none

private theorem fuelBoundedPartialTrace_round_trip :
    ∀ x : FuelBoundedPartialTraceUp,
      fuelBoundedPartialTraceFromEventFlow
        (fuelBoundedPartialTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel substrate initial trace readback refusal transport route provenance name =>
      change
        some
          (fuelBoundedPartialTraceDecodePacket
            (fuelBoundedPartialTraceEncodeBHist fuel)
            (fuelBoundedPartialTraceEncodeBHist substrate)
            (fuelBoundedPartialTraceEncodeBHist initial)
            (fuelBoundedPartialTraceEncodeBHist trace)
            (fuelBoundedPartialTraceEncodeBHist readback)
            (fuelBoundedPartialTraceEncodeBHist refusal)
            (fuelBoundedPartialTraceEncodeBHist transport)
            (fuelBoundedPartialTraceEncodeBHist route)
            (fuelBoundedPartialTraceEncodeBHist provenance)
            (fuelBoundedPartialTraceEncodeBHist name)) =
          some
            (FuelBoundedPartialTraceUp.mk fuel substrate initial trace readback refusal
              transport route provenance name)
      unfold fuelBoundedPartialTraceDecodePacket
      rw [fuelBoundedPartialTrace_decode_encode_bhist fuel,
        fuelBoundedPartialTrace_decode_encode_bhist substrate,
        fuelBoundedPartialTrace_decode_encode_bhist initial,
        fuelBoundedPartialTrace_decode_encode_bhist trace,
        fuelBoundedPartialTrace_decode_encode_bhist readback,
        fuelBoundedPartialTrace_decode_encode_bhist refusal,
        fuelBoundedPartialTrace_decode_encode_bhist transport,
        fuelBoundedPartialTrace_decode_encode_bhist route,
        fuelBoundedPartialTrace_decode_encode_bhist provenance,
        fuelBoundedPartialTrace_decode_encode_bhist name]

private theorem fuelBoundedPartialTraceToEventFlow_injective
    {x y : FuelBoundedPartialTraceUp} :
    fuelBoundedPartialTraceToEventFlow x =
      fuelBoundedPartialTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fuelBoundedPartialTraceFromEventFlow
          (fuelBoundedPartialTraceToEventFlow x) =
        fuelBoundedPartialTraceFromEventFlow
          (fuelBoundedPartialTraceToEventFlow y) :=
    congrArg fuelBoundedPartialTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fuelBoundedPartialTrace_round_trip x).symm
      (Eq.trans hread (fuelBoundedPartialTrace_round_trip y)))

private theorem fuelBoundedPartialTrace_fields_faithful :
    ∀ x y : FuelBoundedPartialTraceUp,
      fuelBoundedPartialTraceFields x = fuelBoundedPartialTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fuel₁ substrate₁ initial₁ trace₁ readback₁ refusal₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk fuel₂ substrate₂ initial₂ trace₂ readback₂ refusal₂ transport₂ route₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance fuelBoundedPartialTraceBHistCarrier :
    BHistCarrier FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fuelBoundedPartialTraceToEventFlow
  fromEventFlow := fuelBoundedPartialTraceFromEventFlow

instance fuelBoundedPartialTraceChapterTasteGate :
    ChapterTasteGate FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fuelBoundedPartialTraceFromEventFlow
        (fuelBoundedPartialTraceToEventFlow x) = some x
    exact fuelBoundedPartialTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fuelBoundedPartialTraceToEventFlow_injective heq)

instance fuelBoundedPartialTraceFieldFaithful :
    FieldFaithful FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fuelBoundedPartialTraceFields
  field_faithful := fuelBoundedPartialTrace_fields_faithful

instance fuelBoundedPartialTraceNontrivial :
    Nontrivial FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FuelBoundedPartialTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FuelBoundedPartialTraceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FuelBoundedPartialTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fuelBoundedPartialTraceChapterTasteGate

theorem FuelBoundedPartialTraceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FuelBoundedPartialTraceUp) ∧
      Nonempty (FieldFaithful FuelBoundedPartialTraceUp) ∧
        Nonempty (Nontrivial FuelBoundedPartialTraceUp) ∧
          (∀ h : BHist,
            fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist h) = h) ∧
            (∀ x : FuelBoundedPartialTraceUp,
              fuelBoundedPartialTraceFromEventFlow
                (fuelBoundedPartialTraceToEventFlow x) = some x) ∧
              (∀ x y : FuelBoundedPartialTraceUp,
                fuelBoundedPartialTraceToEventFlow x =
                    fuelBoundedPartialTraceToEventFlow y →
                  x = y) ∧
                fuelBoundedPartialTraceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨fuelBoundedPartialTraceChapterTasteGate⟩,
      ⟨fuelBoundedPartialTraceFieldFaithful⟩,
      ⟨fuelBoundedPartialTraceNontrivial⟩,
      fuelBoundedPartialTrace_decode_encode_bhist,
      fuelBoundedPartialTrace_round_trip,
      (fun _ _ heq => fuelBoundedPartialTraceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FuelBoundedPartialTraceUp
