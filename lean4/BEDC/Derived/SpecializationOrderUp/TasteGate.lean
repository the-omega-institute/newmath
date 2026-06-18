import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpecializationOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpecializationOrderUp : Type where
  | mk (T O R H C P N : BHist) : SpecializationOrderUp
  deriving DecidableEq

def specializationOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: specializationOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: specializationOrderEncodeBHist h

def specializationOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (specializationOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (specializationOrderDecodeBHist tail)

private theorem SpecializationOrderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, specializationOrderDecodeBHist
      (specializationOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def specializationOrderFields : SpecializationOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpecializationOrderUp.mk T O R H C P N => [T, O, R, H, C, P, N]

def specializationOrderToEventFlow : SpecializationOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (specializationOrderFields x).map specializationOrderEncodeBHist

private def specializationOrderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => specializationOrderEventAtDefault index rest

def specializationOrderFromEventFlow (ef : EventFlow) : Option SpecializationOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SpecializationOrderUp.mk
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 0 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 1 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 2 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 3 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 4 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 5 ef))
      (specializationOrderDecodeBHist (specializationOrderEventAtDefault 6 ef)))

private theorem SpecializationOrderTasteGate_single_carrier_alignment_round_trip
    (x : SpecializationOrderUp) :
    specializationOrderFromEventFlow (specializationOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T O R H C P N =>
      change
        some
          (SpecializationOrderUp.mk
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist T))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist O))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist R))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist H))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist C))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist P))
            (specializationOrderDecodeBHist (specializationOrderEncodeBHist N))) =
          some (SpecializationOrderUp.mk T O R H C P N)
      rw [SpecializationOrderTasteGate_single_carrier_alignment_decode_encode T,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode O,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode R,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode H,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode C,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode P,
        SpecializationOrderTasteGate_single_carrier_alignment_decode_encode N]

private theorem SpecializationOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SpecializationOrderUp} :
    specializationOrderToEventFlow x = specializationOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      specializationOrderFromEventFlow (specializationOrderToEventFlow x) =
        specializationOrderFromEventFlow (specializationOrderToEventFlow y) :=
    congrArg specializationOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SpecializationOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SpecializationOrderTasteGate_single_carrier_alignment_round_trip y)))

instance specializationOrderBHistCarrier : BHistCarrier SpecializationOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := specializationOrderToEventFlow
  fromEventFlow := specializationOrderFromEventFlow

instance specializationOrderChapterTasteGate :
    ChapterTasteGate SpecializationOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change specializationOrderFromEventFlow
      (specializationOrderToEventFlow x) = some x
    exact SpecializationOrderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SpecializationOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SpecializationOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, specializationOrderDecodeBHist
      (specializationOrderEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SpecializationOrderUp) ∧
        Nonempty (ChapterTasteGate SpecializationOrderUp) ∧
          specializationOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SpecializationOrderTasteGate_single_carrier_alignment_decode_encode,
      ⟨specializationOrderBHistCarrier⟩,
      ⟨specializationOrderChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SpecializationOrderUp
