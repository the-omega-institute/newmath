import BEDC.Derived.HeatKernelUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeatKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def heatKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heatKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heatKernelEncodeBHist h

def heatKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heatKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heatKernelDecodeBHist tail)

private theorem HeatKernelTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, heatKernelDecodeBHist (heatKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heatKernelFields : BEDC.Derived.HeatKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.HeatKernelUp.mk W S G Q R H C P N => [W, S, G, Q, R, H, C, P, N]

def heatKernelToEventFlow : BEDC.Derived.HeatKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (heatKernelFields x).map heatKernelEncodeBHist

private def heatKernelEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heatKernelEventAt index rest

def heatKernelFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.HeatKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.HeatKernelUp.mk
      (heatKernelDecodeBHist (heatKernelEventAt 0 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 1 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 2 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 3 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 4 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 5 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 6 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 7 ef))
      (heatKernelDecodeBHist (heatKernelEventAt 8 ef)))

private theorem HeatKernelTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.HeatKernelUp) :
    heatKernelFromEventFlow (heatKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W S G Q R H C P N =>
      change
        some
          (BEDC.Derived.HeatKernelUp.mk
            (heatKernelDecodeBHist (heatKernelEncodeBHist W))
            (heatKernelDecodeBHist (heatKernelEncodeBHist S))
            (heatKernelDecodeBHist (heatKernelEncodeBHist G))
            (heatKernelDecodeBHist (heatKernelEncodeBHist Q))
            (heatKernelDecodeBHist (heatKernelEncodeBHist R))
            (heatKernelDecodeBHist (heatKernelEncodeBHist H))
            (heatKernelDecodeBHist (heatKernelEncodeBHist C))
            (heatKernelDecodeBHist (heatKernelEncodeBHist P))
            (heatKernelDecodeBHist (heatKernelEncodeBHist N))) =
          some (BEDC.Derived.HeatKernelUp.mk W S G Q R H C P N)
      rw [HeatKernelTasteGate_single_carrier_alignment_decode_encode W,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode S,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode G,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode Q,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode R,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode H,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode C,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode P,
        HeatKernelTasteGate_single_carrier_alignment_decode_encode N]

private theorem HeatKernelTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.HeatKernelUp} :
    heatKernelToEventFlow x = heatKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heatKernelFromEventFlow (heatKernelToEventFlow x) =
        heatKernelFromEventFlow (heatKernelToEventFlow y) :=
    congrArg heatKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HeatKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HeatKernelTasteGate_single_carrier_alignment_round_trip y)))

private theorem HeatKernelTasteGate_single_carrier_alignment_fields :
    ∀ x y : BEDC.Derived.HeatKernelUp, heatKernelFields x = heatKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ S₁ G₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ S₂ G₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance heatKernelBHistCarrier : BHistCarrier BEDC.Derived.HeatKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heatKernelToEventFlow
  fromEventFlow := heatKernelFromEventFlow

instance heatKernelChapterTasteGate :
    ChapterTasteGate BEDC.Derived.HeatKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heatKernelFromEventFlow (heatKernelToEventFlow x) = some x
    exact HeatKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HeatKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance heatKernelFieldFaithful : FieldFaithful BEDC.Derived.HeatKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := heatKernelFields
  field_faithful := HeatKernelTasteGate_single_carrier_alignment_fields

instance heatKernelNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BEDC.Derived.HeatKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.HeatKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.HeatKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HeatKernelTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BEDC.Derived.HeatKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heatKernelChapterTasteGate

theorem HeatKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, heatKernelDecodeBHist (heatKernelEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.HeatKernelUp,
        heatKernelFromEventFlow (heatKernelToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.HeatKernelUp,
          heatKernelToEventFlow x = heatKernelToEventFlow y → x = y) ∧
          heatKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact HeatKernelTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact HeatKernelTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact HeatKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.HeatKernelUp
