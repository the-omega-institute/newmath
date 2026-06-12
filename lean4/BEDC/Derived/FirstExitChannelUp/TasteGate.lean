import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FirstExitChannelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FirstExitChannelUp : Type where
  | mk (O B T K L H C P N : BHist) : FirstExitChannelUp
  deriving DecidableEq

def firstExitChannelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: firstExitChannelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: firstExitChannelEncodeBHist h

def firstExitChannelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (firstExitChannelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (firstExitChannelDecodeBHist tail)

private theorem FirstExitChannelTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, firstExitChannelDecodeBHist (firstExitChannelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def firstExitChannelFields : FirstExitChannelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FirstExitChannelUp.mk O B T K L H C P N => [O, B, T, K, L, H, C, P, N]

def firstExitChannelToEventFlow : FirstExitChannelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (firstExitChannelFields x).map firstExitChannelEncodeBHist

private def firstExitChannelEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => firstExitChannelEventAt index rest

def firstExitChannelFromEventFlow (ef : EventFlow) : Option FirstExitChannelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FirstExitChannelUp.mk
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 0 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 1 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 2 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 3 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 4 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 5 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 6 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 7 ef))
      (firstExitChannelDecodeBHist (firstExitChannelEventAt 8 ef)))

private theorem FirstExitChannelTasteGate_single_carrier_alignment_round_trip
    (x : FirstExitChannelUp) :
    firstExitChannelFromEventFlow (firstExitChannelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O B T K L H C P N =>
      change
        some
          (FirstExitChannelUp.mk
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist O))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist B))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist T))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist K))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist L))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist H))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist C))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist P))
            (firstExitChannelDecodeBHist (firstExitChannelEncodeBHist N))) =
          some (FirstExitChannelUp.mk O B T K L H C P N)
      rw [FirstExitChannelTasteGate_single_carrier_alignment_decode_encode O,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode B,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode T,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode K,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode L,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode H,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode C,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode P,
        FirstExitChannelTasteGate_single_carrier_alignment_decode_encode N]

private theorem FirstExitChannelTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FirstExitChannelUp} :
    firstExitChannelToEventFlow x = firstExitChannelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      firstExitChannelFromEventFlow (firstExitChannelToEventFlow x) =
        firstExitChannelFromEventFlow (firstExitChannelToEventFlow y) :=
    congrArg firstExitChannelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FirstExitChannelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FirstExitChannelTasteGate_single_carrier_alignment_round_trip y)))

private theorem FirstExitChannelTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FirstExitChannelUp, firstExitChannelFields x = firstExitChannelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ B₁ T₁ K₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ B₂ T₂ K₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance firstExitChannelBHistCarrier : BHistCarrier FirstExitChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := firstExitChannelToEventFlow
  fromEventFlow := firstExitChannelFromEventFlow

instance firstExitChannelChapterTasteGate : ChapterTasteGate FirstExitChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change firstExitChannelFromEventFlow (firstExitChannelToEventFlow x) = some x
    exact FirstExitChannelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FirstExitChannelTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance firstExitChannelFieldFaithful : FieldFaithful FirstExitChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := firstExitChannelFields
  field_faithful := FirstExitChannelTasteGate_single_carrier_alignment_fields_faithful

instance firstExitChannelNontrivial : Nontrivial FirstExitChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FirstExitChannelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FirstExitChannelUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FirstExitChannelTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FirstExitChannelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  firstExitChannelChapterTasteGate

theorem FirstExitChannelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FirstExitChannelUp) ∧
      Nonempty (FieldFaithful FirstExitChannelUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FirstExitChannelUp) ∧
          (∀ h : BHist, firstExitChannelDecodeBHist (firstExitChannelEncodeBHist h) = h) ∧
            (∀ x : FirstExitChannelUp,
              firstExitChannelFromEventFlow (firstExitChannelToEventFlow x) = some x) ∧
              (∀ x y : FirstExitChannelUp,
                firstExitChannelToEventFlow x = firstExitChannelToEventFlow y → x = y) ∧
                firstExitChannelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨firstExitChannelChapterTasteGate⟩,
      ⟨firstExitChannelFieldFaithful⟩,
      ⟨firstExitChannelNontrivial⟩,
      FirstExitChannelTasteGate_single_carrier_alignment_decode_encode,
      FirstExitChannelTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FirstExitChannelTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FirstExitChannelUp
