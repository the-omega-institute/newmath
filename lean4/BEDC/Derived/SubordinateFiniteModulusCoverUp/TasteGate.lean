import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubordinateFiniteModulusCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubordinateFiniteModulusCoverUp : Type where
  | mk (K F L Q U H R P N : BHist) : SubordinateFiniteModulusCoverUp

def subordinateFiniteModulusCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subordinateFiniteModulusCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subordinateFiniteModulusCoverEncodeBHist h

def subordinateFiniteModulusCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subordinateFiniteModulusCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subordinateFiniteModulusCoverDecodeBHist tail)

private theorem SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subordinateFiniteModulusCoverFields :
    SubordinateFiniteModulusCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubordinateFiniteModulusCoverUp.mk K F L Q U H R P N => [K, F, L, Q, U, H, R, P, N]

def subordinateFiniteModulusCoverToEventFlow :
    SubordinateFiniteModulusCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (subordinateFiniteModulusCoverFields x).map subordinateFiniteModulusCoverEncodeBHist

private def subordinateFiniteModulusCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subordinateFiniteModulusCoverEventAtDefault index rest

def subordinateFiniteModulusCoverFromEventFlow
    (ef : EventFlow) : Option SubordinateFiniteModulusCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubordinateFiniteModulusCoverUp.mk
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 0 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 1 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 2 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 3 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 4 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 5 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 6 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 7 ef))
      (subordinateFiniteModulusCoverDecodeBHist
        (subordinateFiniteModulusCoverEventAtDefault 8 ef)))

private theorem SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SubordinateFiniteModulusCoverUp,
      subordinateFiniteModulusCoverFromEventFlow
          (subordinateFiniteModulusCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F L Q U H R P N =>
      change
        some
          (SubordinateFiniteModulusCoverUp.mk
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist K))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist F))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist L))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist Q))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist U))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist H))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist R))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist P))
            (subordinateFiniteModulusCoverDecodeBHist
              (subordinateFiniteModulusCoverEncodeBHist N))) =
          some (SubordinateFiniteModulusCoverUp.mk K F L Q U H R P N)
      rw [SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode K,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode F,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode L,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode Q,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode U,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode H,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode R,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode P,
        SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode N]

private theorem SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SubordinateFiniteModulusCoverUp} :
    subordinateFiniteModulusCoverToEventFlow x =
      subordinateFiniteModulusCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subordinateFiniteModulusCoverFromEventFlow
          (subordinateFiniteModulusCoverToEventFlow x) =
        subordinateFiniteModulusCoverFromEventFlow
          (subordinateFiniteModulusCoverToEventFlow y) :=
    congrArg subordinateFiniteModulusCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_round_trip y)))

instance subordinateFiniteModulusCoverBHistCarrier :
    BHistCarrier SubordinateFiniteModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subordinateFiniteModulusCoverToEventFlow
  fromEventFlow := subordinateFiniteModulusCoverFromEventFlow

instance subordinateFiniteModulusCoverChapterTasteGate :
    ChapterTasteGate SubordinateFiniteModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subordinateFiniteModulusCoverFromEventFlow
      (subordinateFiniteModulusCoverToEventFlow x) = some x
    exact SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SubordinateFiniteModulusCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subordinateFiniteModulusCoverChapterTasteGate

theorem SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier SubordinateFiniteModulusCoverUp,
        Nonempty (@ChapterTasteGate SubordinateFiniteModulusCoverUp carrier)) ∧
      (∀ h : BHist,
        subordinateFiniteModulusCoverDecodeBHist
          (subordinateFiniteModulusCoverEncodeBHist h) = h) ∧
        (∀ x : SubordinateFiniteModulusCoverUp,
          subordinateFiniteModulusCoverFromEventFlow
            (subordinateFiniteModulusCoverToEventFlow x) = some x) ∧
          subordinateFiniteModulusCoverEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨subordinateFiniteModulusCoverBHistCarrier,
        ⟨subordinateFiniteModulusCoverChapterTasteGate⟩⟩,
      SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_decode,
      SubordinateFiniteModulusCoverTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.SubordinateFiniteModulusCoverUp
