import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProximinalSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProximinalSetUp : Type where
  | mk
      (metric located distance witness realSeal transport continuation provenance localName :
        BHist) : ProximinalSetUp
  deriving DecidableEq

def proximinalSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proximinalSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proximinalSetEncodeBHist h

def proximinalSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proximinalSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proximinalSetDecodeBHist tail)

private theorem ProximinalSetTasteGate_decode_encode :
    ∀ h : BHist, proximinalSetDecodeBHist (proximinalSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def proximinalSetFields : ProximinalSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProximinalSetUp.mk metric located distance witness realSeal transport continuation
      provenance localName =>
      [metric, located, distance, witness, realSeal, transport, continuation, provenance,
        localName]

def proximinalSetToEventFlow : ProximinalSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (proximinalSetFields x).map proximinalSetEncodeBHist

private def proximinalSetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proximinalSetEventAt index rest

def proximinalSetFromEventFlow (ef : EventFlow) : Option ProximinalSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProximinalSetUp.mk
      (proximinalSetDecodeBHist (proximinalSetEventAt 0 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 1 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 2 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 3 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 4 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 5 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 6 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 7 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAt 8 ef)))

private theorem ProximinalSetTasteGate_round_trip (x : ProximinalSetUp) :
    proximinalSetFromEventFlow (proximinalSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk metric located distance witness realSeal transport continuation provenance localName =>
      change
        some
          (ProximinalSetUp.mk
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist metric))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist located))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist distance))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist witness))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist realSeal))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist transport))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist continuation))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist provenance))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist localName))) =
          some
            (ProximinalSetUp.mk metric located distance witness realSeal transport
              continuation provenance localName)
      rw [ProximinalSetTasteGate_decode_encode metric,
        ProximinalSetTasteGate_decode_encode located,
        ProximinalSetTasteGate_decode_encode distance,
        ProximinalSetTasteGate_decode_encode witness,
        ProximinalSetTasteGate_decode_encode realSeal,
        ProximinalSetTasteGate_decode_encode transport,
        ProximinalSetTasteGate_decode_encode continuation,
        ProximinalSetTasteGate_decode_encode provenance,
        ProximinalSetTasteGate_decode_encode localName]

private theorem proximinalSetToEventFlow_injective {x y : ProximinalSetUp} :
    proximinalSetToEventFlow x = proximinalSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proximinalSetFromEventFlow (proximinalSetToEventFlow x) =
        proximinalSetFromEventFlow (proximinalSetToEventFlow y) :=
    congrArg proximinalSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProximinalSetTasteGate_round_trip x).symm
      (Eq.trans hread (ProximinalSetTasteGate_round_trip y)))

private theorem proximinalSet_field_faithful :
    ∀ x y : ProximinalSetUp,
      proximinalSetFields x = proximinalSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric located distance witness realSeal transport continuation provenance localName =>
      cases y with
      | mk metric' located' distance' witness' realSeal' transport' continuation'
          provenance' localName' =>
          cases hfields
          rfl

instance proximinalSetBHistCarrier : BHistCarrier ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proximinalSetToEventFlow
  fromEventFlow := proximinalSetFromEventFlow

instance proximinalSetChapterTasteGate : ChapterTasteGate ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proximinalSetFromEventFlow (proximinalSetToEventFlow x) = some x
    exact ProximinalSetTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proximinalSetToEventFlow_injective heq)

instance proximinalSetFieldFaithful : FieldFaithful ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proximinalSetFields
  field_faithful := proximinalSet_field_faithful

instance proximinalSetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProximinalSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProximinalSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProximinalSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proximinalSetChapterTasteGate

theorem ProximinalSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProximinalSetUp) ∧
      Nonempty (FieldFaithful ProximinalSetUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ProximinalSetUp) ∧
      (∀ h : BHist, proximinalSetDecodeBHist (proximinalSetEncodeBHist h) = h) ∧
      (∀ x : ProximinalSetUp,
        proximinalSetFromEventFlow (proximinalSetToEventFlow x) = some x) ∧
      (∀ x y : ProximinalSetUp,
        proximinalSetToEventFlow x = proximinalSetToEventFlow y → x = y) ∧
      proximinalSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨proximinalSetChapterTasteGate⟩,
      ⟨proximinalSetFieldFaithful⟩,
      ⟨proximinalSetNontrivial⟩,
      ProximinalSetTasteGate_decode_encode,
      ProximinalSetTasteGate_round_trip,
      (fun _ _ heq => proximinalSetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProximinalSetUp
