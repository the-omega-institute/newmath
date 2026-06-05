import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnchorSubcubeTriggerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnchorSubcubeTriggerUp : Type where
  | mk (A B S R G K H C P N : BHist) : AnchorSubcubeTriggerUp
  deriving DecidableEq

def anchorSubcubeTriggerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: anchorSubcubeTriggerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: anchorSubcubeTriggerEncodeBHist h

def anchorSubcubeTriggerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (anchorSubcubeTriggerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (anchorSubcubeTriggerDecodeBHist tail)

private theorem AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def anchorSubcubeTriggerFields : AnchorSubcubeTriggerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorSubcubeTriggerUp.mk A B S R G K H C P N => [A, B, S, R, G, K, H, C, P, N]

def anchorSubcubeTriggerToEventFlow : AnchorSubcubeTriggerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => anchorSubcubeTriggerFields x |>.map anchorSubcubeTriggerEncodeBHist

private def anchorSubcubeTriggerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => anchorSubcubeTriggerRawAt n rest

def anchorSubcubeTriggerFromEventFlow (flow : EventFlow) : Option AnchorSubcubeTriggerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AnchorSubcubeTriggerUp.mk
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 0 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 1 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 2 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 3 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 4 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 5 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 6 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 7 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 8 flow))
      (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerRawAt 9 flow)))

private theorem AnchorSubcubeTriggerTasteGate_single_carrier_alignment_round_trip
    (x : AnchorSubcubeTriggerUp) :
    anchorSubcubeTriggerFromEventFlow (anchorSubcubeTriggerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B S R G K H C P N =>
      change
        some
          (AnchorSubcubeTriggerUp.mk
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist A))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist B))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist S))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist R))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist G))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist K))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist H))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist C))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist P))
            (anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist N))) =
          some (AnchorSubcubeTriggerUp.mk A B S R G K H C P N)
      rw [AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode A,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode B,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode S,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode R,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode G,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode K,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode H,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode C,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode P,
        AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode N]

private theorem AnchorSubcubeTriggerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AnchorSubcubeTriggerUp} :
    anchorSubcubeTriggerToEventFlow x = anchorSubcubeTriggerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      anchorSubcubeTriggerFromEventFlow (anchorSubcubeTriggerToEventFlow x) =
        anchorSubcubeTriggerFromEventFlow (anchorSubcubeTriggerToEventFlow y) :=
    congrArg anchorSubcubeTriggerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AnchorSubcubeTriggerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AnchorSubcubeTriggerTasteGate_single_carrier_alignment_round_trip y)))

private theorem AnchorSubcubeTriggerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AnchorSubcubeTriggerUp,
      anchorSubcubeTriggerFields x = anchorSubcubeTriggerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ S₁ R₁ G₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ S₂ R₂ G₂ K₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance anchorSubcubeTriggerBHistCarrier : BHistCarrier AnchorSubcubeTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := anchorSubcubeTriggerToEventFlow
  fromEventFlow := anchorSubcubeTriggerFromEventFlow

instance anchorSubcubeTriggerChapterTasteGate : ChapterTasteGate AnchorSubcubeTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change anchorSubcubeTriggerFromEventFlow (anchorSubcubeTriggerToEventFlow x) = some x
    exact AnchorSubcubeTriggerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AnchorSubcubeTriggerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance anchorSubcubeTriggerFieldFaithful : FieldFaithful AnchorSubcubeTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := anchorSubcubeTriggerFields
  field_faithful := AnchorSubcubeTriggerTasteGate_single_carrier_alignment_fields_faithful

instance anchorSubcubeTriggerNontrivial : Nontrivial AnchorSubcubeTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AnchorSubcubeTriggerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AnchorSubcubeTriggerUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnchorSubcubeTriggerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  anchorSubcubeTriggerChapterTasteGate

theorem AnchorSubcubeTriggerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      anchorSubcubeTriggerDecodeBHist (anchorSubcubeTriggerEncodeBHist h) = h) ∧
      (∀ x : AnchorSubcubeTriggerUp,
        anchorSubcubeTriggerFromEventFlow (anchorSubcubeTriggerToEventFlow x) = some x) ∧
      ChapterTasteGate AnchorSubcubeTriggerUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨AnchorSubcubeTriggerTasteGate_single_carrier_alignment_decode_encode,
      AnchorSubcubeTriggerTasteGate_single_carrier_alignment_round_trip,
      anchorSubcubeTriggerChapterTasteGate⟩

end BEDC.Derived.AnchorSubcubeTriggerUp
