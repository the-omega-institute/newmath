import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCauchySelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCauchySelectorUp : Type where
  | mk (Q M I W R D E H C P N : BHist) : SequentialCauchySelectorUp
  deriving DecidableEq

def sequentialCauchySelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCauchySelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCauchySelectorEncodeBHist h

def sequentialCauchySelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCauchySelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCauchySelectorDecodeBHist tail)

private theorem SequentialCauchySelectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialCauchySelectorFields : SequentialCauchySelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCauchySelectorUp.mk Q M I W R D E H C P N =>
      [Q, M, I, W, R, D, E, H, C, P, N]

def sequentialCauchySelectorToEventFlow : SequentialCauchySelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialCauchySelectorFields x).map sequentialCauchySelectorEncodeBHist

private def sequentialCauchySelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialCauchySelectorEventAtDefault index rest

def sequentialCauchySelectorFromEventFlow (ef : EventFlow) :
    Option SequentialCauchySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialCauchySelectorUp.mk
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 0 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 1 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 2 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 3 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 4 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 5 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 6 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 7 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 8 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 9 ef))
      (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEventAtDefault 10 ef)))

private theorem SequentialCauchySelectorTasteGate_single_carrier_alignment_round_trip
    (x : SequentialCauchySelectorUp) :
    sequentialCauchySelectorFromEventFlow (sequentialCauchySelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q M I W R D E H C P N =>
      change
        some
          (SequentialCauchySelectorUp.mk
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist Q))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist M))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist I))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist W))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist R))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist D))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist E))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist H))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist C))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist P))
            (sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist N))) =
          some (SequentialCauchySelectorUp.mk Q M I W R D E H C P N)
      rw [SequentialCauchySelectorTasteGate_single_carrier_alignment_decode Q,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode M,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode I,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode W,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode R,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode D,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode E,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode H,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode C,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode P,
        SequentialCauchySelectorTasteGate_single_carrier_alignment_decode N]

private theorem SequentialCauchySelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialCauchySelectorUp} :
    sequentialCauchySelectorToEventFlow x = sequentialCauchySelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCauchySelectorFromEventFlow (sequentialCauchySelectorToEventFlow x) =
        sequentialCauchySelectorFromEventFlow (sequentialCauchySelectorToEventFlow y) :=
    congrArg sequentialCauchySelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialCauchySelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialCauchySelectorTasteGate_single_carrier_alignment_round_trip y)))

instance sequentialCauchySelectorBHistCarrier :
    BHistCarrier SequentialCauchySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCauchySelectorToEventFlow
  fromEventFlow := sequentialCauchySelectorFromEventFlow

instance sequentialCauchySelectorChapterTasteGate :
    ChapterTasteGate SequentialCauchySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCauchySelectorFromEventFlow
      (sequentialCauchySelectorToEventFlow x) = some x
    exact SequentialCauchySelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialCauchySelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SequentialCauchySelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialCauchySelectorDecodeBHist (sequentialCauchySelectorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentialCauchySelectorUp) ∧
        Nonempty (ChapterTasteGate SequentialCauchySelectorUp) ∧
          sequentialCauchySelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SequentialCauchySelectorTasteGate_single_carrier_alignment_decode,
      ⟨sequentialCauchySelectorBHistCarrier⟩,
      ⟨sequentialCauchySelectorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SequentialCauchySelectorUp
