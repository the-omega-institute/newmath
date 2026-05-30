import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CaratheodoryConvexHullUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CaratheodoryConvexHullUp : Type where
  | mk (A C S W F L B Y H T P N : BHist) : CaratheodoryConvexHullUp
  deriving DecidableEq

def caratheodoryConvexHullEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: caratheodoryConvexHullEncodeBHist h
  | BHist.e1 h => BMark.b1 :: caratheodoryConvexHullEncodeBHist h

def caratheodoryConvexHullDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => caratheodoryConvexHullDecodeBHist tail |> BHist.e0
  | BMark.b1 :: tail => caratheodoryConvexHullDecodeBHist tail |> BHist.e1

private theorem CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, caratheodoryConvexHullDecodeBHist
      (caratheodoryConvexHullEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def caratheodoryConvexHullFields : CaratheodoryConvexHullUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CaratheodoryConvexHullUp.mk A C S W F L B Y H T P N =>
      [A, C, S, W, F, L, B, Y, H, T, P, N]

def caratheodoryConvexHullToEventFlow : CaratheodoryConvexHullUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (caratheodoryConvexHullFields x).map caratheodoryConvexHullEncodeBHist

private def caratheodoryConvexHullEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => caratheodoryConvexHullEventAt index rest

def caratheodoryConvexHullFromEventFlow (ef : EventFlow) :
    Option CaratheodoryConvexHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CaratheodoryConvexHullUp.mk
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 0 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 1 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 2 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 3 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 4 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 5 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 6 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 7 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 8 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 9 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 10 ef))
      (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEventAt 11 ef)))

private theorem CaratheodoryConvexHullTasteGate_single_carrier_alignment_round_trip
    (x : CaratheodoryConvexHullUp) :
    caratheodoryConvexHullFromEventFlow (caratheodoryConvexHullToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A C S W F L B Y H T P N =>
      change
        some
          (CaratheodoryConvexHullUp.mk
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist A))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist C))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist S))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist W))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist F))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist L))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist B))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist Y))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist H))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist T))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist P))
            (caratheodoryConvexHullDecodeBHist (caratheodoryConvexHullEncodeBHist N))) =
          some (CaratheodoryConvexHullUp.mk A C S W F L B Y H T P N)
      rw [CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode A,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode C,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode S,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode W,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode F,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode L,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode B,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode Y,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode H,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode T,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode P,
        CaratheodoryConvexHullTasteGate_single_carrier_alignment_decode_encode N]

private theorem CaratheodoryConvexHullTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CaratheodoryConvexHullUp} :
    caratheodoryConvexHullToEventFlow x = caratheodoryConvexHullToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      caratheodoryConvexHullFromEventFlow (caratheodoryConvexHullToEventFlow x) =
        caratheodoryConvexHullFromEventFlow (caratheodoryConvexHullToEventFlow y) :=
    congrArg caratheodoryConvexHullFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CaratheodoryConvexHullTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CaratheodoryConvexHullTasteGate_single_carrier_alignment_round_trip y)))

private theorem CaratheodoryConvexHullTasteGate_single_carrier_alignment_fields :
    ∀ x y : CaratheodoryConvexHullUp,
      caratheodoryConvexHullFields x = caratheodoryConvexHullFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ C₁ S₁ W₁ F₁ L₁ B₁ Y₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk A₂ C₂ S₂ W₂ F₂ L₂ B₂ Y₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance caratheodoryConvexHullBHistCarrier : BHistCarrier CaratheodoryConvexHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := caratheodoryConvexHullToEventFlow
  fromEventFlow := caratheodoryConvexHullFromEventFlow

instance caratheodoryConvexHullChapterTasteGate :
    ChapterTasteGate CaratheodoryConvexHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change caratheodoryConvexHullFromEventFlow
      (caratheodoryConvexHullToEventFlow x) = some x
    exact CaratheodoryConvexHullTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CaratheodoryConvexHullTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance caratheodoryConvexHullFieldFaithful :
    FieldFaithful CaratheodoryConvexHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := caratheodoryConvexHullFields
  field_faithful := CaratheodoryConvexHullTasteGate_single_carrier_alignment_fields

instance caratheodoryConvexHullNontrivial : Nontrivial CaratheodoryConvexHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CaratheodoryConvexHullUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CaratheodoryConvexHullUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CaratheodoryConvexHullTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CaratheodoryConvexHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  caratheodoryConvexHullChapterTasteGate

theorem CaratheodoryConvexHullTasteGate_single_carrier_alignment :
    caratheodoryConvexHullEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  rfl

end BEDC.Derived.CaratheodoryConvexHullUp
