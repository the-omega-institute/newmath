import BEDC.Derived.BrouwerFixedPointUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def brouwerFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerFixedPointEncodeBHist h

def brouwerFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerFixedPointDecodeBHist tail)

private theorem brouwerFixedPoint_decode_encode_bhist :
    ∀ h : BHist, brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerFixedPointFields : BrouwerFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerFixedPointUp.mk K S D L W E H C P N => [K, S, D, L, W, E, H, C, P, N]

def brouwerFixedPointToEventFlow : BrouwerFixedPointUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerFixedPointFields x).map brouwerFixedPointEncodeBHist

private def brouwerFixedPointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerFixedPointEventAtDefault index rest

def brouwerFixedPointFromEventFlow (ef : EventFlow) : Option BrouwerFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerFixedPointUp.mk
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 0 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 1 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 2 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 3 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 4 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 5 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 6 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 7 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 8 ef))
      (brouwerFixedPointDecodeBHist (brouwerFixedPointEventAtDefault 9 ef)))

private theorem brouwerFixedPoint_round_trip :
    ∀ x : BrouwerFixedPointUp,
      brouwerFixedPointFromEventFlow (brouwerFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K S D L W E H C P N =>
      change
        some
          (BrouwerFixedPointUp.mk
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist K))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist S))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist D))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist L))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist W))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist E))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist H))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist C))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist P))
            (brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist N))) =
          some (BrouwerFixedPointUp.mk K S D L W E H C P N)
      rw [brouwerFixedPoint_decode_encode_bhist K, brouwerFixedPoint_decode_encode_bhist S,
        brouwerFixedPoint_decode_encode_bhist D, brouwerFixedPoint_decode_encode_bhist L,
        brouwerFixedPoint_decode_encode_bhist W, brouwerFixedPoint_decode_encode_bhist E,
        brouwerFixedPoint_decode_encode_bhist H, brouwerFixedPoint_decode_encode_bhist C,
        brouwerFixedPoint_decode_encode_bhist P, brouwerFixedPoint_decode_encode_bhist N]

private theorem brouwerFixedPointToEventFlow_injective {x y : BrouwerFixedPointUp} :
    brouwerFixedPointToEventFlow x = brouwerFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerFixedPointFromEventFlow (brouwerFixedPointToEventFlow x) =
        brouwerFixedPointFromEventFlow (brouwerFixedPointToEventFlow y) :=
    congrArg brouwerFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (brouwerFixedPoint_round_trip x).symm
      (Eq.trans hread (brouwerFixedPoint_round_trip y)))

private theorem brouwerFixedPoint_field_faithful :
    ∀ x y : BrouwerFixedPointUp, brouwerFixedPointFields x = brouwerFixedPointFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K S D L W E H C P N =>
      cases y with
      | mk K' S' D' L' W' E' H' C' P' N' =>
          cases hfields
          rfl

instance brouwerFixedPointBHistCarrier : BHistCarrier BrouwerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerFixedPointToEventFlow
  fromEventFlow := brouwerFixedPointFromEventFlow

instance brouwerFixedPointChapterTasteGate : ChapterTasteGate BrouwerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerFixedPointFromEventFlow (brouwerFixedPointToEventFlow x) = some x
    exact brouwerFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerFixedPointToEventFlow_injective heq)

instance brouwerFixedPointFieldFaithful : FieldFaithful BrouwerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerFixedPointFields
  field_faithful := brouwerFixedPoint_field_faithful

instance brouwerFixedPointNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BrouwerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerFixedPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BrouwerFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerFixedPointChapterTasteGate

theorem BrouwerFixedPointTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BrouwerFixedPointUp) ∧
      Nonempty (FieldFaithful BrouwerFixedPointUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BrouwerFixedPointUp) ∧
      (∀ h : BHist, brouwerFixedPointDecodeBHist (brouwerFixedPointEncodeBHist h) = h) ∧
      (∀ x : BrouwerFixedPointUp,
        brouwerFixedPointFromEventFlow (brouwerFixedPointToEventFlow x) = some x) ∧
      (∀ x y : BrouwerFixedPointUp,
        brouwerFixedPointToEventFlow x = brouwerFixedPointToEventFlow y → x = y) ∧
      brouwerFixedPointEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨brouwerFixedPointChapterTasteGate⟩, ⟨brouwerFixedPointFieldFaithful⟩,
      ⟨brouwerFixedPointNontrivial⟩, brouwerFixedPoint_decode_encode_bhist,
      brouwerFixedPoint_round_trip,
      (fun _ _ heq => brouwerFixedPointToEventFlow_injective heq), rfl⟩

end BEDC.Derived.BrouwerFixedPointUp
