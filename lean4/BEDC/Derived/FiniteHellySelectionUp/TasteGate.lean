import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteHellySelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteHellySelectionUp : Type where
  | mk (I D W Q R S H C P N : BHist) : FiniteHellySelectionUp
  deriving DecidableEq

def finiteHellySelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteHellySelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteHellySelectionEncodeBHist h

def finiteHellySelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteHellySelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteHellySelectionDecodeBHist tail)

private theorem FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteHellySelectionDecodeBHist
      (finiteHellySelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteHellySelectionToEventFlow : FiniteHellySelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHellySelectionUp.mk I D W Q R S H C P N =>
      [[BMark.b0],
        finiteHellySelectionEncodeBHist I,
        [BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteHellySelectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteHellySelectionEncodeBHist N]

private def finiteHellySelectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteHellySelectionEventAtDefault index rest

def finiteHellySelectionFromEventFlow (ef : EventFlow) :
    Option FiniteHellySelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteHellySelectionUp.mk
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 1 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 3 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 5 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 7 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 9 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 11 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 13 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 15 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 17 ef))
      (finiteHellySelectionDecodeBHist (finiteHellySelectionEventAtDefault 19 ef)))

private theorem FiniteHellySelectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteHellySelectionUp,
      finiteHellySelectionFromEventFlow (finiteHellySelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D W Q R S H C P N =>
      change
        some
            (FiniteHellySelectionUp.mk
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist I))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist D))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist W))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist Q))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist R))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist S))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist H))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist C))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist P))
              (finiteHellySelectionDecodeBHist (finiteHellySelectionEncodeBHist N))) =
          some (FiniteHellySelectionUp.mk I D W Q R S H C P N)
      rw [FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode I,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode D,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode W,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode Q,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode R,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode S,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode H,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode C,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode P,
        FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteHellySelectionToEventFlow_injective
    {x y : FiniteHellySelectionUp} :
    finiteHellySelectionToEventFlow x = finiteHellySelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteHellySelectionFromEventFlow (finiteHellySelectionToEventFlow x) =
        finiteHellySelectionFromEventFlow (finiteHellySelectionToEventFlow y) :=
    congrArg finiteHellySelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteHellySelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteHellySelectionTasteGate_single_carrier_alignment_round_trip y)))

instance finiteHellySelectionBHistCarrier : BHistCarrier FiniteHellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteHellySelectionToEventFlow
  fromEventFlow := finiteHellySelectionFromEventFlow

instance finiteHellySelectionChapterTasteGate : ChapterTasteGate FiniteHellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteHellySelectionFromEventFlow (finiteHellySelectionToEventFlow x) = some x
    exact FiniteHellySelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteHellySelectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteHellySelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteHellySelectionChapterTasteGate

theorem FiniteHellySelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteHellySelectionDecodeBHist
      (finiteHellySelectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteHellySelectionUp) ∧
        Nonempty (ChapterTasteGate FiniteHellySelectionUp) ∧
          finiteHellySelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FiniteHellySelectionTasteGate_single_carrier_alignment_decode_encode,
      ⟨finiteHellySelectionBHistCarrier⟩,
      ⟨finiteHellySelectionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteHellySelectionUp
