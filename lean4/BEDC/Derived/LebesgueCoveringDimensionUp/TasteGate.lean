import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueCoveringDimensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueCoveringDimensionUp : Type where
  | mk (X U V R O B F H C P N : BHist) : LebesgueCoveringDimensionUp
  deriving DecidableEq

def lebesgueCoveringDimensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueCoveringDimensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueCoveringDimensionEncodeBHist h

def lebesgueCoveringDimensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueCoveringDimensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueCoveringDimensionDecodeBHist tail)

private theorem LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lebesgueCoveringDimensionFields : LebesgueCoveringDimensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueCoveringDimensionUp.mk X U V R O B F H C P N => [X, U, V, R, O, B, F, H, C, P, N]

def lebesgueCoveringDimensionToEventFlow : LebesgueCoveringDimensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lebesgueCoveringDimensionFields x).map lebesgueCoveringDimensionEncodeBHist

private def lebesgueCoveringDimensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lebesgueCoveringDimensionEventAtDefault index rest

def lebesgueCoveringDimensionFromEventFlow : EventFlow → Option LebesgueCoveringDimensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LebesgueCoveringDimensionUp.mk
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 0 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 1 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 2 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 3 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 4 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 5 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 6 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 7 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 8 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 9 ef))
          (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEventAtDefault 10 ef)))

private theorem LebesgueCoveringDimensionTasteGate_single_carrier_alignment_round_trip
    (x : LebesgueCoveringDimensionUp) :
    lebesgueCoveringDimensionFromEventFlow (lebesgueCoveringDimensionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X U V R O B F H C P N =>
      change
        some
          (LebesgueCoveringDimensionUp.mk
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist X))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist U))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist V))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist R))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist O))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist B))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist F))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist H))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist C))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist P))
            (lebesgueCoveringDimensionDecodeBHist (lebesgueCoveringDimensionEncodeBHist N))) =
          some (LebesgueCoveringDimensionUp.mk X U V R O B F H C P N)
      rw [LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode X,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode U,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode V,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode R,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode O,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode B,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode F,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode H,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode C,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode P,
        LebesgueCoveringDimensionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LebesgueCoveringDimensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LebesgueCoveringDimensionUp} :
    lebesgueCoveringDimensionToEventFlow x = lebesgueCoveringDimensionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueCoveringDimensionFromEventFlow (lebesgueCoveringDimensionToEventFlow x) =
        lebesgueCoveringDimensionFromEventFlow (lebesgueCoveringDimensionToEventFlow y) :=
    congrArg lebesgueCoveringDimensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LebesgueCoveringDimensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LebesgueCoveringDimensionTasteGate_single_carrier_alignment_round_trip y)))

instance lebesgueCoveringDimensionBHistCarrier :
    BHistCarrier LebesgueCoveringDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueCoveringDimensionToEventFlow
  fromEventFlow := lebesgueCoveringDimensionFromEventFlow

instance lebesgueCoveringDimensionChapterTasteGate :
    ChapterTasteGate LebesgueCoveringDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      lebesgueCoveringDimensionFromEventFlow (lebesgueCoveringDimensionToEventFlow x) =
        some x
    exact LebesgueCoveringDimensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LebesgueCoveringDimensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LebesgueCoveringDimensionTasteGate_single_carrier_alignment :
    ChapterTasteGate LebesgueCoveringDimensionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact lebesgueCoveringDimensionChapterTasteGate

end BEDC.Derived.LebesgueCoveringDimensionUp
