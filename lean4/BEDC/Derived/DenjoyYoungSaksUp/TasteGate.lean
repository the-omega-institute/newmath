import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenjoyYoungSaksUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenjoyYoungSaksUp : Type where
  | mk
      (I F U L O S R D E H C P N : BHist) :
      DenjoyYoungSaksUp
  deriving DecidableEq

def DenjoyYoungSaksTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b1]

def denjoyYoungSaksEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denjoyYoungSaksEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denjoyYoungSaksEncodeBHist h

def denjoyYoungSaksDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denjoyYoungSaksDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denjoyYoungSaksDecodeBHist tail)

private theorem DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow :
    DenjoyYoungSaksUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DenjoyYoungSaksUp.mk I F U L O S R D E H C P N =>
      [DenjoyYoungSaksTasteGate_single_carrier_alignment_tag,
        denjoyYoungSaksEncodeBHist I,
        denjoyYoungSaksEncodeBHist F,
        denjoyYoungSaksEncodeBHist U,
        denjoyYoungSaksEncodeBHist L,
        denjoyYoungSaksEncodeBHist O,
        denjoyYoungSaksEncodeBHist S,
        denjoyYoungSaksEncodeBHist R,
        denjoyYoungSaksEncodeBHist D,
        denjoyYoungSaksEncodeBHist E,
        denjoyYoungSaksEncodeBHist H,
        denjoyYoungSaksEncodeBHist C,
        denjoyYoungSaksEncodeBHist P,
        denjoyYoungSaksEncodeBHist N]

private def DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault index rest

def DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DenjoyYoungSaksUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenjoyYoungSaksUp.mk
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 12 ef))
      (denjoyYoungSaksDecodeBHist
        (DenjoyYoungSaksTasteGate_single_carrier_alignment_eventAtDefault 13 ef)))

private theorem DenjoyYoungSaksTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DenjoyYoungSaksUp,
      DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow
          (DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F U L O S R D E H C P N =>
      change
        some
          (DenjoyYoungSaksUp.mk
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist I))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist F))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist U))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist L))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist O))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist S))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist R))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist D))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist E))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist H))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist C))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist P))
            (denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist N))) =
          some (DenjoyYoungSaksUp.mk I F U L O S R D E H C P N)
      rw [DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode I,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode F,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode U,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode L,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode O,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode S,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode R,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode D,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode E,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode H,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode C,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode P,
        DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode N]

private theorem DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DenjoyYoungSaksUp} :
    DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow x =
        DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow
          (DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow x) =
        DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow
          (DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DenjoyYoungSaksTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DenjoyYoungSaksTasteGate_single_carrier_alignment_round_trip y)))

instance denjoyYoungSaksBHistCarrier : BHistCarrier DenjoyYoungSaksUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow

instance denjoyYoungSaksChapterTasteGate : ChapterTasteGate DenjoyYoungSaksUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DenjoyYoungSaksTasteGate_single_carrier_alignment_fromEventFlow
          (DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DenjoyYoungSaksTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenjoyYoungSaksTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DenjoyYoungSaksTasteGate_single_carrier_alignment :
    (∀ h : BHist, denjoyYoungSaksDecodeBHist (denjoyYoungSaksEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DenjoyYoungSaksUp) ∧
        Nonempty (ChapterTasteGate DenjoyYoungSaksUp) ∧
          denjoyYoungSaksEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DenjoyYoungSaksTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro denjoyYoungSaksBHistCarrier,
      Nonempty.intro denjoyYoungSaksChapterTasteGate,
      rfl⟩

end BEDC.Derived.DenjoyYoungSaksUp
