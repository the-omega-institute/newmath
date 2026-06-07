import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompactIntervalSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompactIntervalSelectionUp : Type where
  | mk (I B N D S R E H C P Q : BHist) : LocatedCompactIntervalSelectionUp

def locatedCompactIntervalSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompactIntervalSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompactIntervalSelectionEncodeBHist h

def locatedCompactIntervalSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompactIntervalSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompactIntervalSelectionDecodeBHist tail)

private theorem locatedCompactIntervalSelectionDecode_encode_bhist :
    ∀ h : BHist,
      locatedCompactIntervalSelectionDecodeBHist
          (locatedCompactIntervalSelectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompactIntervalSelectionFields :
    LocatedCompactIntervalSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompactIntervalSelectionUp.mk I B N D S R E H C P Q =>
      [I, B, N, D, S, R, E, H, C, P, Q]

def locatedCompactIntervalSelectionToEventFlow :
    LocatedCompactIntervalSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => locatedCompactIntervalSelectionFields x |>.map locatedCompactIntervalSelectionEncodeBHist

private def locatedCompactIntervalSelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, event :: _rest => event
  | Nat.zero, [] => []
  | Nat.succ index, _event :: rest => locatedCompactIntervalSelectionEventAt index rest
  | Nat.succ _index, [] => []

def locatedCompactIntervalSelectionFromEventFlow
    (ef : EventFlow) : Option LocatedCompactIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompactIntervalSelectionUp.mk
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 0 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 1 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 2 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 3 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 4 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 5 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 6 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 7 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 8 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 9 ef))
      (locatedCompactIntervalSelectionDecodeBHist
        (locatedCompactIntervalSelectionEventAt 10 ef)))

private theorem locatedCompactIntervalSelection_round_trip
    (x : LocatedCompactIntervalSelectionUp) :
    locatedCompactIntervalSelectionFromEventFlow
        (locatedCompactIntervalSelectionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I B N D S R E H C P Q =>
      change
        some
            (LocatedCompactIntervalSelectionUp.mk
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist I))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist B))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist N))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist D))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist S))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist R))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist E))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist H))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist C))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist P))
              (locatedCompactIntervalSelectionDecodeBHist
                (locatedCompactIntervalSelectionEncodeBHist Q))) =
          some (LocatedCompactIntervalSelectionUp.mk I B N D S R E H C P Q)
      rw [locatedCompactIntervalSelectionDecode_encode_bhist I,
        locatedCompactIntervalSelectionDecode_encode_bhist B,
        locatedCompactIntervalSelectionDecode_encode_bhist N,
        locatedCompactIntervalSelectionDecode_encode_bhist D,
        locatedCompactIntervalSelectionDecode_encode_bhist S,
        locatedCompactIntervalSelectionDecode_encode_bhist R,
        locatedCompactIntervalSelectionDecode_encode_bhist E,
        locatedCompactIntervalSelectionDecode_encode_bhist H,
        locatedCompactIntervalSelectionDecode_encode_bhist C,
        locatedCompactIntervalSelectionDecode_encode_bhist P,
        locatedCompactIntervalSelectionDecode_encode_bhist Q]

private theorem locatedCompactIntervalSelectionToEventFlow_injective
    {x y : LocatedCompactIntervalSelectionUp} :
    locatedCompactIntervalSelectionToEventFlow x =
        locatedCompactIntervalSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompactIntervalSelectionFromEventFlow
          (locatedCompactIntervalSelectionToEventFlow x) =
        locatedCompactIntervalSelectionFromEventFlow
          (locatedCompactIntervalSelectionToEventFlow y) :=
    congrArg locatedCompactIntervalSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCompactIntervalSelection_round_trip x).symm
      (Eq.trans hread (locatedCompactIntervalSelection_round_trip y)))

instance locatedCompactIntervalSelectionBHistCarrier :
    BHistCarrier LocatedCompactIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompactIntervalSelectionToEventFlow
  fromEventFlow := locatedCompactIntervalSelectionFromEventFlow

instance locatedCompactIntervalSelectionChapterTasteGate :
    ChapterTasteGate LocatedCompactIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCompactIntervalSelectionFromEventFlow
          (locatedCompactIntervalSelectionToEventFlow x) =
        some x
    exact locatedCompactIntervalSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompactIntervalSelectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCompactIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompactIntervalSelectionChapterTasteGate

theorem LocatedCompactIntervalSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCompactIntervalSelectionDecodeBHist
          (locatedCompactIntervalSelectionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier LocatedCompactIntervalSelectionUp) ∧
        Nonempty (ChapterTasteGate LocatedCompactIntervalSelectionUp) ∧
          locatedCompactIntervalSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locatedCompactIntervalSelectionDecode_encode_bhist,
      ⟨⟨locatedCompactIntervalSelectionBHistCarrier⟩,
        ⟨⟨locatedCompactIntervalSelectionChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.LocatedCompactIntervalSelectionUp
