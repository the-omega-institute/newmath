import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HigsonCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HigsonCompactificationUp : Type where
  | mk (U M A C F R S B H T P N : BHist) : HigsonCompactificationUp
  deriving DecidableEq

def higsonCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: higsonCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: higsonCompactificationEncodeBHist h

def higsonCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (higsonCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (higsonCompactificationDecodeBHist tail)

private theorem HigsonCompactificationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def higsonCompactificationFields : HigsonCompactificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HigsonCompactificationUp.mk U M A C F R S B H T P N =>
      [U, M, A, C, F, R, S, B, H, T, P, N]

def higsonCompactificationToEventFlow : HigsonCompactificationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (higsonCompactificationFields x).map higsonCompactificationEncodeBHist

private def higsonCompactificationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => higsonCompactificationEventAtDefault index rest

def higsonCompactificationFromEventFlow
    (ef : EventFlow) : Option HigsonCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HigsonCompactificationUp.mk
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 0 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 1 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 2 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 3 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 4 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 5 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 6 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 7 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 8 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 9 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 10 ef))
      (higsonCompactificationDecodeBHist (higsonCompactificationEventAtDefault 11 ef)))

private theorem HigsonCompactificationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HigsonCompactificationUp,
      higsonCompactificationFromEventFlow (higsonCompactificationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M A C F R S B H T P N =>
      change
        some
          (HigsonCompactificationUp.mk
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist U))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist M))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist A))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist C))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist F))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist R))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist S))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist B))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist H))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist T))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist P))
            (higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist N))) =
          some (HigsonCompactificationUp.mk U M A C F R S B H T P N)
      rw [HigsonCompactificationTasteGate_single_carrier_alignment_decode U,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode M,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode A,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode C,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode F,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode R,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode S,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode B,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode H,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode T,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode P,
        HigsonCompactificationTasteGate_single_carrier_alignment_decode N]

private theorem HigsonCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HigsonCompactificationUp} :
    higsonCompactificationToEventFlow x = higsonCompactificationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      higsonCompactificationFromEventFlow (higsonCompactificationToEventFlow x) =
        higsonCompactificationFromEventFlow (higsonCompactificationToEventFlow y) :=
    congrArg higsonCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HigsonCompactificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HigsonCompactificationTasteGate_single_carrier_alignment_round_trip y)))

instance higsonCompactificationBHistCarrier : BHistCarrier HigsonCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := higsonCompactificationToEventFlow
  fromEventFlow := higsonCompactificationFromEventFlow

instance higsonCompactificationChapterTasteGate :
    ChapterTasteGate HigsonCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change higsonCompactificationFromEventFlow (higsonCompactificationToEventFlow x) =
      some x
    exact HigsonCompactificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro _x _y hxy heq
    exact hxy
      (HigsonCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HigsonCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  higsonCompactificationChapterTasteGate

theorem HigsonCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      higsonCompactificationDecodeBHist (higsonCompactificationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HigsonCompactificationUp) ∧
        Nonempty (ChapterTasteGate HigsonCompactificationUp) ∧
          higsonCompactificationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HigsonCompactificationTasteGate_single_carrier_alignment_decode,
      ⟨higsonCompactificationBHistCarrier⟩,
      ⟨higsonCompactificationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HigsonCompactificationUp
