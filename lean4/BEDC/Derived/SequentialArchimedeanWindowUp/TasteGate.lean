import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialArchimedeanWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialArchimedeanWindowUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (R i Q D A G E H C P N : BHist) : SequentialArchimedeanWindowUp
  deriving DecidableEq

def sequentialArchimedeanWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialArchimedeanWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialArchimedeanWindowEncodeBHist h

def sequentialArchimedeanWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialArchimedeanWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialArchimedeanWindowDecodeBHist tail)

private theorem SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialArchimedeanWindowFields : SequentialArchimedeanWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialArchimedeanWindowUp.mk R i Q D A G E H C P N =>
      [R, i, Q, D, A, G, E, H, C, P, N]

def sequentialArchimedeanWindowToEventFlow : SequentialArchimedeanWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialArchimedeanWindowFields x).map sequentialArchimedeanWindowEncodeBHist

private def sequentialArchimedeanWindowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialArchimedeanWindowEventAt index rest

def sequentialArchimedeanWindowFromEventFlow
    (ef : EventFlow) : Option SequentialArchimedeanWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialArchimedeanWindowUp.mk
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 0 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 1 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 2 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 3 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 4 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 5 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 6 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 7 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 8 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 9 ef))
      (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEventAt 10 ef)))

private theorem SequentialArchimedeanWindowTasteGate_single_carrier_alignment_round_trip
    (x : SequentialArchimedeanWindowUp) :
    sequentialArchimedeanWindowFromEventFlow (sequentialArchimedeanWindowToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R i Q D A G E H C P N =>
      change
        some
          (SequentialArchimedeanWindowUp.mk
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist R))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist i))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist Q))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist D))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist A))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist G))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist E))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist H))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist C))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist P))
            (sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist N))) =
          some (SequentialArchimedeanWindowUp.mk R i Q D A G E H C P N)
      rw [SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode R,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode i,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode Q,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode D,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode A,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode G,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode E,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode H,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode C,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode P,
        SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode N]

private theorem SequentialArchimedeanWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialArchimedeanWindowUp} :
    sequentialArchimedeanWindowToEventFlow x = sequentialArchimedeanWindowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialArchimedeanWindowFromEventFlow (sequentialArchimedeanWindowToEventFlow x) =
        sequentialArchimedeanWindowFromEventFlow (sequentialArchimedeanWindowToEventFlow y) :=
    congrArg sequentialArchimedeanWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialArchimedeanWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialArchimedeanWindowTasteGate_single_carrier_alignment_round_trip y)))

instance sequentialArchimedeanWindowBHistCarrier :
    BHistCarrier SequentialArchimedeanWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialArchimedeanWindowToEventFlow
  fromEventFlow := sequentialArchimedeanWindowFromEventFlow

instance sequentialArchimedeanWindowChapterTasteGate :
    ChapterTasteGate SequentialArchimedeanWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialArchimedeanWindowFromEventFlow (sequentialArchimedeanWindowToEventFlow x) =
        some x
    exact SequentialArchimedeanWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialArchimedeanWindowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SequentialArchimedeanWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialArchimedeanWindowChapterTasteGate

theorem SequentialArchimedeanWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialArchimedeanWindowDecodeBHist (sequentialArchimedeanWindowEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate SequentialArchimedeanWindowUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SequentialArchimedeanWindowTasteGate_single_carrier_alignment_decode,
      ⟨sequentialArchimedeanWindowChapterTasteGate⟩⟩

end BEDC.Derived.SequentialArchimedeanWindowUp
