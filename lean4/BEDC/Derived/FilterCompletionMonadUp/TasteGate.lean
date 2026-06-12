import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterCompletionMonadUp : Type where
  | mk (Q B Z S R D E U F A H C P N : BHist) : FilterCompletionMonadUp
  deriving DecidableEq

def filterCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterCompletionMonadEncodeBHist h

def filterCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterCompletionMonadDecodeBHist tail)

private theorem FilterCompletionMonadTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterCompletionMonadFields : FilterCompletionMonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterCompletionMonadUp.mk Q B Z S R D E U F A H C P N =>
      [Q, B, Z, S, R, D, E, U, F, A, H, C, P, N]

def filterCompletionMonadToEventFlow : FilterCompletionMonadUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterCompletionMonadFields x).map filterCompletionMonadEncodeBHist

private def filterCompletionMonadEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterCompletionMonadEventAtDefault index rest

def filterCompletionMonadFromEventFlow : EventFlow → Option FilterCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FilterCompletionMonadUp.mk
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 0 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 1 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 2 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 3 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 4 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 5 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 6 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 7 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 8 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 9 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 10 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 11 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 12 ef))
        (filterCompletionMonadDecodeBHist (filterCompletionMonadEventAtDefault 13 ef)))

private theorem FilterCompletionMonadTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FilterCompletionMonadUp,
      filterCompletionMonadFromEventFlow (filterCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q B Z S R D E U F A H C P N =>
      change
        some
          (FilterCompletionMonadUp.mk
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist Q))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist B))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist Z))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist S))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist R))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist D))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist E))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist U))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist F))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist A))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist H))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist C))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist P))
            (filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist N))) =
          some (FilterCompletionMonadUp.mk Q B Z S R D E U F A H C P N)
      rw [FilterCompletionMonadTasteGate_single_carrier_alignment_decode Q,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode B,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode Z,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode S,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode R,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode D,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode E,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode U,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode F,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode A,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode H,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode C,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode P,
        FilterCompletionMonadTasteGate_single_carrier_alignment_decode N]

private theorem FilterCompletionMonadTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FilterCompletionMonadUp} :
    filterCompletionMonadToEventFlow x = filterCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterCompletionMonadFromEventFlow (filterCompletionMonadToEventFlow x) =
        filterCompletionMonadFromEventFlow (filterCompletionMonadToEventFlow y) :=
    congrArg filterCompletionMonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FilterCompletionMonadTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FilterCompletionMonadTasteGate_single_carrier_alignment_round_trip y)))

instance filterCompletionMonadBHistCarrier : BHistCarrier FilterCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterCompletionMonadToEventFlow
  fromEventFlow := filterCompletionMonadFromEventFlow

instance filterCompletionMonadChapterTasteGate : ChapterTasteGate FilterCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filterCompletionMonadFromEventFlow (filterCompletionMonadToEventFlow x) = some x
    exact FilterCompletionMonadTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FilterCompletionMonadTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FilterCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterCompletionMonadChapterTasteGate

theorem FilterCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist, filterCompletionMonadDecodeBHist (filterCompletionMonadEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FilterCompletionMonadUp) ∧
        Nonempty (ChapterTasteGate FilterCompletionMonadUp) ∧
          filterCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FilterCompletionMonadTasteGate_single_carrier_alignment_decode,
      ⟨filterCompletionMonadBHistCarrier⟩,
      ⟨filterCompletionMonadChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FilterCompletionMonadUp
