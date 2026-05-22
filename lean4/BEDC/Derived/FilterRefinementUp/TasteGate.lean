import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterRefinementUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterRefinementUp : Type where
  | mk (S T rho lambda H C P N : BHist) : FilterRefinementUp
  deriving DecidableEq

def FilterRefinementTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      FilterRefinementTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      FilterRefinementTasteGate_single_carrier_alignment_encodeBHist h

def FilterRefinementTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FilterRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
        (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FilterRefinementTasteGate_single_carrier_alignment_fields :
    FilterRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterRefinementUp.mk S T rho lambda H C P N => [S, T, rho, lambda, H, C, P, N]

def FilterRefinementTasteGate_single_carrier_alignment_toEventFlow :
    FilterRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FilterRefinementTasteGate_single_carrier_alignment_fields x).map
      FilterRefinementTasteGate_single_carrier_alignment_encodeBHist

private def FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault index rest

def FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FilterRefinementUp.mk
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
          (FilterRefinementTasteGate_single_carrier_alignment_eventAtDefault 7 ef)))

private theorem FilterRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FilterRefinementUp,
      FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow
        (FilterRefinementTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T rho lambda H C P N =>
      change
        some
          (FilterRefinementUp.mk
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist S))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist T))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist rho))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist lambda))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist H))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist C))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist P))
            (FilterRefinementTasteGate_single_carrier_alignment_decodeBHist
              (FilterRefinementTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (FilterRefinementUp.mk S T rho lambda H C P N)
      rw [FilterRefinementTasteGate_single_carrier_alignment_decode S,
        FilterRefinementTasteGate_single_carrier_alignment_decode T,
        FilterRefinementTasteGate_single_carrier_alignment_decode rho,
        FilterRefinementTasteGate_single_carrier_alignment_decode lambda,
        FilterRefinementTasteGate_single_carrier_alignment_decode H,
        FilterRefinementTasteGate_single_carrier_alignment_decode C,
        FilterRefinementTasteGate_single_carrier_alignment_decode P,
        FilterRefinementTasteGate_single_carrier_alignment_decode N]

private theorem FilterRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FilterRefinementUp} :
    FilterRefinementTasteGate_single_carrier_alignment_toEventFlow x =
      FilterRefinementTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (FilterRefinementTasteGate_single_carrier_alignment_toEventFlow x) =
        FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (FilterRefinementTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FilterRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FilterRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance filterRefinementBHistCarrier : BHistCarrier FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FilterRefinementTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow

instance filterRefinementChapterTasteGate :
    ChapterTasteGate FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FilterRefinementTasteGate_single_carrier_alignment_fromEventFlow
        (FilterRefinementTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact FilterRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FilterRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FilterRefinementTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FilterRefinementUp) ∧
      Nonempty (ChapterTasteGate FilterRefinementUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨filterRefinementBHistCarrier⟩, ⟨filterRefinementChapterTasteGate⟩⟩

end BEDC.Derived.FilterRefinementUp.TasteGate
