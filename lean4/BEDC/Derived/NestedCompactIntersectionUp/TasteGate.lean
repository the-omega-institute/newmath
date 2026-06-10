import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedCompactIntersectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedCompactIntersectionUp : Type where
  | mk (C J W F S R E H P N : BHist) : NestedCompactIntersectionUp
  deriving DecidableEq

def nestedCompactIntersectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedCompactIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedCompactIntersectionEncodeBHist h

def nestedCompactIntersectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedCompactIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedCompactIntersectionDecodeBHist tail)

private theorem NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedCompactIntersectionFields : NestedCompactIntersectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedCompactIntersectionUp.mk C J W F S R E H P N => [C, J, W, F, S, R, E, H, P, N]

def nestedCompactIntersectionToEventFlow : NestedCompactIntersectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedCompactIntersectionFields x).map nestedCompactIntersectionEncodeBHist

private def nestedCompactIntersectionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedCompactIntersectionEventAt index rest

def nestedCompactIntersectionFromEventFlow (ef : EventFlow) :
    Option NestedCompactIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedCompactIntersectionUp.mk
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 0 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 1 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 2 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 3 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 4 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 5 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 6 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 7 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 8 ef))
      (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEventAt 9 ef)))

private theorem NestedCompactIntersectionTasteGate_single_carrier_alignment_round_trip
    (x : NestedCompactIntersectionUp) :
    nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C J W F S R E H P N =>
      change
        some
          (NestedCompactIntersectionUp.mk
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist C))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist J))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist W))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist F))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist S))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist R))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist E))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist H))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist P))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist N))) =
          some (NestedCompactIntersectionUp.mk C J W F S R E H P N)
      rw [NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode C,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode J,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode W,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode F,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode S,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode R,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode E,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode H,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode P,
        NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem NestedCompactIntersectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedCompactIntersectionUp} :
    nestedCompactIntersectionToEventFlow x = nestedCompactIntersectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow x) =
        nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow y) :=
    congrArg nestedCompactIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedCompactIntersectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NestedCompactIntersectionTasteGate_single_carrier_alignment_round_trip y)))

instance nestedCompactIntersectionBHistCarrier :
    BHistCarrier NestedCompactIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedCompactIntersectionToEventFlow
  fromEventFlow := nestedCompactIntersectionFromEventFlow

instance nestedCompactIntersectionChapterTasteGate :
    ChapterTasteGate NestedCompactIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow x) =
        some x
    exact NestedCompactIntersectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedCompactIntersectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NestedCompactIntersectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NestedCompactIntersectionUp) ∧
        Nonempty (ChapterTasteGate NestedCompactIntersectionUp) ∧
          nestedCompactIntersectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NestedCompactIntersectionTasteGate_single_carrier_alignment_decode_encode,
      ⟨nestedCompactIntersectionBHistCarrier⟩,
      ⟨nestedCompactIntersectionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NestedCompactIntersectionUp.TasteGate
