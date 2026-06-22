import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusTailFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusTailFusionUp : Type where
  | mk (K U T W R E H C P L N : BHist) : CompactModulusTailFusionUp
  deriving DecidableEq

def CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist h

def CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactModulusTailFusionTasteGate_single_carrier_alignment_fields :
    CompactModulusTailFusionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusTailFusionUp.mk K U T W R E H C P L N =>
      [K, U, T, W, R, E, H, C, P, L, N]

def CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow :
    CompactModulusTailFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CompactModulusTailFusionTasteGate_single_carrier_alignment_fields x).map
        CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist

private def CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt index rest

def CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CompactModulusTailFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactModulusTailFusionUp.mk
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 0 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 1 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 2 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 3 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 4 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 5 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 6 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 7 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 8 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 9 ef))
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem CompactModulusTailFusionTasteGate_single_carrier_alignment_round_trip
    (x : CompactModulusTailFusionUp) :
    CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow
        (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K U T W R E H C P L N =>
      change
        some
          (CompactModulusTailFusionUp.mk
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist K))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist U))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist T))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist W))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist R))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist E))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist H))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist C))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist P))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist L))
            (CompactModulusTailFusionTasteGate_single_carrier_alignment_decodeBHist
              (CompactModulusTailFusionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CompactModulusTailFusionUp.mk K U T W R E H C P L N)
      rw [CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode K,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode U,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode T,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode W,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode R,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode E,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode H,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode C,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode P,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode L,
        CompactModulusTailFusionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactModulusTailFusionUp} :
    CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow x =
        CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow x) =
        CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactModulusTailFusionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactModulusTailFusionTasteGate_single_carrier_alignment_round_trip y)))

instance compactModulusTailFusionBHistCarrier :
    BHistCarrier CompactModulusTailFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow

instance compactModulusTailFusionChapterTasteGate :
    ChapterTasteGate CompactModulusTailFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompactModulusTailFusionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactModulusTailFusionTasteGate_single_carrier_alignment :
    ChapterTasteGate CompactModulusTailFusionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      CompactModulusTailFusionTasteGate_single_carrier_alignment_fromEventFlow
          (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompactModulusTailFusionTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy
      (CompactModulusTailFusionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.CompactModulusTailFusionUp
