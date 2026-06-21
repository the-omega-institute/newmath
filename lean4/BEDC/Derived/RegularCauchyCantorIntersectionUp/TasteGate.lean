import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCantorIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCantorIntersectionUp : Type where
  | mk (I W D T R E H C P N : BHist) : RegularCauchyCantorIntersectionUp
  deriving DecidableEq

def regularCauchyCantorIntersectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCantorIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCantorIntersectionEncodeBHist h

def regularCauchyCantorIntersectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCantorIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCantorIntersectionDecodeBHist tail)

private theorem regularCauchyCantorIntersection_decode_encode :
    ∀ h : BHist,
      regularCauchyCantorIntersectionDecodeBHist
          (regularCauchyCantorIntersectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCantorIntersectionToEventFlow :
    RegularCauchyCantorIntersectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCantorIntersectionUp.mk I W D T R E H C P N =>
      [regularCauchyCantorIntersectionEncodeBHist I,
        regularCauchyCantorIntersectionEncodeBHist W,
        regularCauchyCantorIntersectionEncodeBHist D,
        regularCauchyCantorIntersectionEncodeBHist T,
        regularCauchyCantorIntersectionEncodeBHist R,
        regularCauchyCantorIntersectionEncodeBHist E,
        regularCauchyCantorIntersectionEncodeBHist H,
        regularCauchyCantorIntersectionEncodeBHist C,
        regularCauchyCantorIntersectionEncodeBHist P,
        regularCauchyCantorIntersectionEncodeBHist N]

private def regularCauchyCantorIntersectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCantorIntersectionEventAt index rest

def regularCauchyCantorIntersectionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCantorIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCantorIntersectionUp.mk
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 0 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 1 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 2 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 3 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 4 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 5 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 6 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 7 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 8 ef))
      (regularCauchyCantorIntersectionDecodeBHist
        (regularCauchyCantorIntersectionEventAt 9 ef)))

private theorem regularCauchyCantorIntersection_round_trip
    (x : RegularCauchyCantorIntersectionUp) :
    regularCauchyCantorIntersectionFromEventFlow
        (regularCauchyCantorIntersectionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I W D T R E H C P N =>
      change
        some
          (RegularCauchyCantorIntersectionUp.mk
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist I))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist W))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist D))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist T))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist R))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist E))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist H))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist C))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist P))
            (regularCauchyCantorIntersectionDecodeBHist
              (regularCauchyCantorIntersectionEncodeBHist N))) =
          some (RegularCauchyCantorIntersectionUp.mk I W D T R E H C P N)
      rw [regularCauchyCantorIntersection_decode_encode I,
        regularCauchyCantorIntersection_decode_encode W,
        regularCauchyCantorIntersection_decode_encode D,
        regularCauchyCantorIntersection_decode_encode T,
        regularCauchyCantorIntersection_decode_encode R,
        regularCauchyCantorIntersection_decode_encode E,
        regularCauchyCantorIntersection_decode_encode H,
        regularCauchyCantorIntersection_decode_encode C,
        regularCauchyCantorIntersection_decode_encode P,
        regularCauchyCantorIntersection_decode_encode N]

private theorem regularCauchyCantorIntersectionToEventFlow_injective
    {x y : RegularCauchyCantorIntersectionUp} :
    regularCauchyCantorIntersectionToEventFlow x =
        regularCauchyCantorIntersectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCantorIntersectionFromEventFlow
          (regularCauchyCantorIntersectionToEventFlow x) =
        regularCauchyCantorIntersectionFromEventFlow
          (regularCauchyCantorIntersectionToEventFlow y) :=
    congrArg regularCauchyCantorIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCantorIntersection_round_trip x).symm
      (Eq.trans hread (regularCauchyCantorIntersection_round_trip y)))

instance regularCauchyCantorIntersectionBHistCarrier :
    BHistCarrier RegularCauchyCantorIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCantorIntersectionToEventFlow
  fromEventFlow := regularCauchyCantorIntersectionFromEventFlow

instance regularCauchyCantorIntersectionChapterTasteGate :
    ChapterTasteGate RegularCauchyCantorIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCantorIntersectionFromEventFlow
          (regularCauchyCantorIntersectionToEventFlow x) =
        some x
    exact regularCauchyCantorIntersection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCantorIntersectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyCantorIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCantorIntersectionChapterTasteGate

theorem RegularCauchyCantorIntersectionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyCantorIntersectionUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyCantorIntersectionUp) ∧
        regularCauchyCantorIntersectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularCauchyCantorIntersectionBHistCarrier⟩,
      ⟨regularCauchyCantorIntersectionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RegularCauchyCantorIntersectionUp
