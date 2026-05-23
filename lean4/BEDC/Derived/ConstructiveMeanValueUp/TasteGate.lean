import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveMeanValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveMeanValueUp : Type where
  | mk (I S R D W E H C P N : BHist) : ConstructiveMeanValueUp
  deriving DecidableEq

def constructiveMeanValueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveMeanValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveMeanValueEncodeBHist h

def constructiveMeanValueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveMeanValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveMeanValueDecodeBHist tail)

private theorem ConstructiveMeanValueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveMeanValueFields : ConstructiveMeanValueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveMeanValueUp.mk I S R D W E H C P N => [I, S, R, D, W, E, H, C, P, N]

def constructiveMeanValueToEventFlow : ConstructiveMeanValueUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveMeanValueFields x).map constructiveMeanValueEncodeBHist

private def constructiveMeanValueEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveMeanValueEventAtDefault index rest

def constructiveMeanValueFromEventFlow : EventFlow → Option ConstructiveMeanValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ConstructiveMeanValueUp.mk
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 0 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 1 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 2 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 3 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 4 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 5 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 6 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 7 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 8 ef))
        (constructiveMeanValueDecodeBHist (constructiveMeanValueEventAtDefault 9 ef)))

private theorem ConstructiveMeanValueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveMeanValueUp,
      constructiveMeanValueFromEventFlow (constructiveMeanValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S R D W E H C P N =>
      change
        some
          (ConstructiveMeanValueUp.mk
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist I))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist S))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist R))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist D))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist W))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist E))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist H))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist C))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist P))
            (constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist N))) =
          some (ConstructiveMeanValueUp.mk I S R D W E H C P N)
      rw [ConstructiveMeanValueTasteGate_single_carrier_alignment_decode I,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode S,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode R,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode D,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode W,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode E,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode H,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode C,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode P,
        ConstructiveMeanValueTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveMeanValueTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveMeanValueUp} :
    constructiveMeanValueToEventFlow x = constructiveMeanValueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveMeanValueFromEventFlow (constructiveMeanValueToEventFlow x) =
        constructiveMeanValueFromEventFlow (constructiveMeanValueToEventFlow y) :=
    congrArg constructiveMeanValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstructiveMeanValueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConstructiveMeanValueTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveMeanValueBHistCarrier : BHistCarrier ConstructiveMeanValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveMeanValueToEventFlow
  fromEventFlow := constructiveMeanValueFromEventFlow

instance constructiveMeanValueChapterTasteGate : ChapterTasteGate ConstructiveMeanValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveMeanValueFromEventFlow (constructiveMeanValueToEventFlow x) = some x
    exact ConstructiveMeanValueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveMeanValueTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstructiveMeanValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveMeanValueChapterTasteGate

theorem ConstructiveMeanValueTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveMeanValueDecodeBHist (constructiveMeanValueEncodeBHist h) = h) ∧
      (∀ x : ConstructiveMeanValueUp,
        constructiveMeanValueFromEventFlow (constructiveMeanValueToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveMeanValueUp,
          constructiveMeanValueToEventFlow x = constructiveMeanValueToEventFlow y → x = y) ∧
          constructiveMeanValueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveMeanValueTasteGate_single_carrier_alignment_decode,
      ConstructiveMeanValueTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveMeanValueTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConstructiveMeanValueUp
