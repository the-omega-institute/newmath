import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterBaseUp : Type where
  | mk (I E D R H C P N : BHist) : FilterBaseUp
  deriving DecidableEq

def filterBaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterBaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterBaseEncodeBHist h

def filterBaseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterBaseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterBaseDecodeBHist tail)

private theorem FilterBaseTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, filterBaseDecodeBHist (filterBaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterBaseFields : FilterBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterBaseUp.mk I E D R H C P N => [I, E, D, R, H, C, P, N]

def filterBaseToEventFlow : FilterBaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (filterBaseFields x).map filterBaseEncodeBHist

private def filterBaseEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterBaseEventAt index rest

def filterBaseFromEventFlow (ef : EventFlow) : Option FilterBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterBaseUp.mk
      (filterBaseDecodeBHist (filterBaseEventAt 0 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 1 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 2 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 3 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 4 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 5 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 6 ef))
      (filterBaseDecodeBHist (filterBaseEventAt 7 ef)))

private theorem FilterBaseTasteGate_single_carrier_alignment_round_trip
    (x : FilterBaseUp) :
    filterBaseFromEventFlow (filterBaseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I E D R H C P N =>
      change
        some
          (FilterBaseUp.mk
            (filterBaseDecodeBHist (filterBaseEncodeBHist I))
            (filterBaseDecodeBHist (filterBaseEncodeBHist E))
            (filterBaseDecodeBHist (filterBaseEncodeBHist D))
            (filterBaseDecodeBHist (filterBaseEncodeBHist R))
            (filterBaseDecodeBHist (filterBaseEncodeBHist H))
            (filterBaseDecodeBHist (filterBaseEncodeBHist C))
            (filterBaseDecodeBHist (filterBaseEncodeBHist P))
            (filterBaseDecodeBHist (filterBaseEncodeBHist N))) =
          some (FilterBaseUp.mk I E D R H C P N)
      rw [FilterBaseTasteGate_single_carrier_alignment_decode_encode I,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode E,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode D,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode R,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode H,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode C,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode P,
        FilterBaseTasteGate_single_carrier_alignment_decode_encode N]

private theorem FilterBaseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FilterBaseUp} :
    filterBaseToEventFlow x = filterBaseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterBaseFromEventFlow (filterBaseToEventFlow x) =
        filterBaseFromEventFlow (filterBaseToEventFlow y) :=
    congrArg filterBaseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FilterBaseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FilterBaseTasteGate_single_carrier_alignment_round_trip y)))

instance filterBaseBHistCarrier : BHistCarrier FilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterBaseToEventFlow
  fromEventFlow := filterBaseFromEventFlow

instance filterBaseChapterTasteGate : ChapterTasteGate FilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filterBaseFromEventFlow (filterBaseToEventFlow x) = some x
    exact FilterBaseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FilterBaseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def FilterBaseTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FilterBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterBaseChapterTasteGate

theorem FilterBaseTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FilterBaseUp) ∧
      Nonempty (ChapterTasteGate FilterBaseUp) ∧ hsame BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate hsame
  exact ⟨⟨filterBaseBHistCarrier⟩, ⟨filterBaseChapterTasteGate⟩, hsame_refl BHist.Empty⟩

end BEDC.Derived.FilterBaseUp
