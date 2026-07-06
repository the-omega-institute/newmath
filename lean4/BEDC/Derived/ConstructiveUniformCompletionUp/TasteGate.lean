import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveUniformCompletionUp : Type where
  | mk (S F T W R D E H C P N : BHist) : ConstructiveUniformCompletionUp
  deriving DecidableEq

def constructiveUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveUniformCompletionEncodeBHist h

def constructiveUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveUniformCompletionDecodeBHist tail)

private theorem ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveUniformCompletionFields :
    ConstructiveUniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveUniformCompletionUp.mk S F T W R D E H C P N =>
      [S, F, T, W, R, D, E, H, C, P, N]

def constructiveUniformCompletionToEventFlow :
    ConstructiveUniformCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveUniformCompletionFields x).map
    constructiveUniformCompletionEncodeBHist

private def constructiveUniformCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      constructiveUniformCompletionRawAt index rest

def constructiveUniformCompletionFromEventFlow
    (flow : EventFlow) : Option ConstructiveUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveUniformCompletionUp.mk
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 0 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 1 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 2 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 3 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 4 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 5 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 6 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 7 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 8 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 9 flow))
      (constructiveUniformCompletionDecodeBHist
        (constructiveUniformCompletionRawAt 10 flow)))

private theorem ConstructiveUniformCompletionTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveUniformCompletionUp) :
    constructiveUniformCompletionFromEventFlow
        (constructiveUniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S F T W R D E H C P N =>
      change
        some
          (ConstructiveUniformCompletionUp.mk
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist S))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist F))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist T))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist W))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist R))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist D))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist E))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist H))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist C))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist P))
            (constructiveUniformCompletionDecodeBHist
              (constructiveUniformCompletionEncodeBHist N))) =
          some (ConstructiveUniformCompletionUp.mk S F T W R D E H C P N)
      rw [ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode S,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode F,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode T,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode W,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode R,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode D,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode E,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode H,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode C,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode P,
        ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode N]

private theorem constructiveUniformCompletionToEventFlow_injective
    {x y : ConstructiveUniformCompletionUp} :
    constructiveUniformCompletionToEventFlow x =
        constructiveUniformCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveUniformCompletionFromEventFlow
          (constructiveUniformCompletionToEventFlow x) =
        constructiveUniformCompletionFromEventFlow
          (constructiveUniformCompletionToEventFlow y) :=
    congrArg constructiveUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveUniformCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveUniformCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveUniformCompletionBHistCarrier :
    BHistCarrier ConstructiveUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveUniformCompletionToEventFlow
  fromEventFlow := constructiveUniformCompletionFromEventFlow

instance constructiveUniformCompletionChapterTasteGate :
    ChapterTasteGate ConstructiveUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveUniformCompletionFromEventFlow
          (constructiveUniformCompletionToEventFlow x) = some x
    exact ConstructiveUniformCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveUniformCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstructiveUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveUniformCompletionChapterTasteGate

theorem ConstructiveUniformCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConstructiveUniformCompletionUp) ∧
      (∀ h : BHist,
        constructiveUniformCompletionDecodeBHist
          (constructiveUniformCompletionEncodeBHist h) = h) ∧
        constructiveUniformCompletionEncodeBHist (BHist.e0 BHist.Empty) =
          [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨constructiveUniformCompletionChapterTasteGate⟩
  constructor
  · exact ConstructiveUniformCompletionTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.ConstructiveUniformCompletionUp
