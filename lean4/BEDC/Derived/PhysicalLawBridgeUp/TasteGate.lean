import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalLawBridgeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalLawBridgeUp : Type where
  | mk : (L E B O F G H C Q N : BHist) → PhysicalLawBridgeUp
  deriving DecidableEq

def physicalLawBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalLawBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalLawBridgeEncodeBHist h

def physicalLawBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalLawBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalLawBridgeDecodeBHist tail)

private theorem physicalLawBridge_decode_encode_bhist :
    ∀ h : BHist, physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def physicalLawBridgeFields : PhysicalLawBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalLawBridgeUp.mk L E B O F G H C Q N => [L, E, B, O, F, G, H, C, Q, N]

def physicalLawBridgeToEventFlow : PhysicalLawBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (physicalLawBridgeFields x).map physicalLawBridgeEncodeBHist

private def physicalLawBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => physicalLawBridgeEventAtDefault index rest

def physicalLawBridgeFromEventFlow (ef : EventFlow) : Option PhysicalLawBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhysicalLawBridgeUp.mk
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 0 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 1 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 2 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 3 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 4 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 5 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 6 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 7 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 8 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 9 ef)))

private theorem physicalLawBridge_round_trip :
    ∀ x : PhysicalLawBridgeUp,
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L E B O F G H C Q N =>
      change
        some
          (PhysicalLawBridgeUp.mk
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist L))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist E))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist B))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist O))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist F))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist G))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist H))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist C))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist Q))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist N))) =
          some (PhysicalLawBridgeUp.mk L E B O F G H C Q N)
      rw [physicalLawBridge_decode_encode_bhist L,
        physicalLawBridge_decode_encode_bhist E,
        physicalLawBridge_decode_encode_bhist B,
        physicalLawBridge_decode_encode_bhist O,
        physicalLawBridge_decode_encode_bhist F,
        physicalLawBridge_decode_encode_bhist G,
        physicalLawBridge_decode_encode_bhist H,
        physicalLawBridge_decode_encode_bhist C,
        physicalLawBridge_decode_encode_bhist Q,
        physicalLawBridge_decode_encode_bhist N]

private theorem physicalLawBridgeToEventFlow_injective {x y : PhysicalLawBridgeUp} :
    physicalLawBridgeToEventFlow x = physicalLawBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) =
        physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow y) :=
    congrArg physicalLawBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalLawBridge_round_trip x).symm
      (Eq.trans hread (physicalLawBridge_round_trip y)))

private theorem physicalLawBridge_field_faithful :
    ∀ x y : PhysicalLawBridgeUp, physicalLawBridgeFields x = physicalLawBridgeFields y → x = y :=
  by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk L₁ E₁ B₁ O₁ F₁ G₁ H₁ C₁ Q₁ N₁ =>
        cases y with
        | mk L₂ E₂ B₂ O₂ F₂ G₂ H₂ C₂ Q₂ N₂ =>
            cases hfields
            rfl

instance physicalLawBridgeBHistCarrier : BHistCarrier PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalLawBridgeToEventFlow
  fromEventFlow := physicalLawBridgeFromEventFlow

instance physicalLawBridgeChapterTasteGate : ChapterTasteGate PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x
    exact physicalLawBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalLawBridgeToEventFlow_injective heq)

instance physicalLawBridgeFieldFaithful : FieldFaithful PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalLawBridgeFields
  field_faithful := physicalLawBridge_field_faithful

instance physicalLawBridgeNontrivial : Nontrivial PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalLawBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalLawBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalLawBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalLawBridgeChapterTasteGate

theorem PhysicalLawBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h) ∧
      (physicalLawBridgeEncodeBHist BHist.Empty = []) ∧
        (physicalLawBridgeEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0]) ∧
          (∀ x : PhysicalLawBridgeUp,
            physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x) ∧
            Nonempty (ChapterTasteGate PhysicalLawBridgeUp) ∧
              Nonempty (Nontrivial PhysicalLawBridgeUp) ∧
                Nonempty (FieldFaithful PhysicalLawBridgeUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact physicalLawBridge_decode_encode_bhist
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · exact physicalLawBridge_round_trip
        · constructor
          · exact ⟨physicalLawBridgeChapterTasteGate⟩
          · constructor
            · exact ⟨physicalLawBridgeNontrivial⟩
            · exact ⟨physicalLawBridgeFieldFaithful⟩

end BEDC.Derived.PhysicalLawBridgeUp.TasteGate
