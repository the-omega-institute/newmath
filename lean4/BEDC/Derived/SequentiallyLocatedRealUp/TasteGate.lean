import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentiallyLocatedRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentiallyLocatedRealUp : Type where
  | mk (I S E L R Q H C P N : BHist) : SequentiallyLocatedRealUp
  deriving DecidableEq

def sequentiallyLocatedRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentiallyLocatedRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentiallyLocatedRealEncodeBHist h

def sequentiallyLocatedRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentiallyLocatedRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentiallyLocatedRealDecodeBHist tail)

private theorem SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentiallyLocatedRealFields : SequentiallyLocatedRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentiallyLocatedRealUp.mk I S E L R Q H C P N => [I, S, E, L, R, Q, H, C, P, N]

def sequentiallyLocatedRealToEventFlow : SequentiallyLocatedRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentiallyLocatedRealFields x).map sequentiallyLocatedRealEncodeBHist

private def sequentiallyLocatedRealEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentiallyLocatedRealEventAtDefault index rest

def sequentiallyLocatedRealFromEventFlow (ef : EventFlow) : Option SequentiallyLocatedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentiallyLocatedRealUp.mk
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 0 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 1 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 2 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 3 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 4 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 5 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 6 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 7 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 8 ef))
      (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEventAtDefault 9 ef)))

private theorem SequentiallyLocatedRealTasteGate_single_carrier_alignment_round_trip :
    forall x : SequentiallyLocatedRealUp,
      sequentiallyLocatedRealFromEventFlow (sequentiallyLocatedRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S E L R Q H C P N =>
      change
        some
            (SequentiallyLocatedRealUp.mk
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist I))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist S))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist E))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist L))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist R))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist Q))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist H))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist C))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist P))
              (sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist N))) =
          some (SequentiallyLocatedRealUp.mk I S E L R Q H C P N)
      rw [SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode I,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode S,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode E,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode L,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode R,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode Q,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode H,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode C,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode P,
        SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode N]

private theorem SequentiallyLocatedRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentiallyLocatedRealUp} :
    sequentiallyLocatedRealToEventFlow x = sequentiallyLocatedRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentiallyLocatedRealFromEventFlow (sequentiallyLocatedRealToEventFlow x) =
        sequentiallyLocatedRealFromEventFlow (sequentiallyLocatedRealToEventFlow y) :=
    congrArg sequentiallyLocatedRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentiallyLocatedRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentiallyLocatedRealTasteGate_single_carrier_alignment_round_trip y)))

instance sequentiallyLocatedRealBHistCarrier : BHistCarrier SequentiallyLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentiallyLocatedRealToEventFlow
  fromEventFlow := sequentiallyLocatedRealFromEventFlow

instance sequentiallyLocatedRealChapterTasteGate :
    ChapterTasteGate SequentiallyLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentiallyLocatedRealFromEventFlow (sequentiallyLocatedRealToEventFlow x) = some x
    exact SequentiallyLocatedRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentiallyLocatedRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SequentiallyLocatedRealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      sequentiallyLocatedRealDecodeBHist (sequentiallyLocatedRealEncodeBHist h) = h) ∧
      (forall x : SequentiallyLocatedRealUp,
        sequentiallyLocatedRealFromEventFlow (sequentiallyLocatedRealToEventFlow x) = some x) ∧
        (forall x y : SequentiallyLocatedRealUp,
          sequentiallyLocatedRealToEventFlow x = sequentiallyLocatedRealToEventFlow y -> x = y) ∧
          sequentiallyLocatedRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SequentiallyLocatedRealTasteGate_single_carrier_alignment_decode,
      ⟨SequentiallyLocatedRealTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          SequentiallyLocatedRealTasteGate_single_carrier_alignment_toEventFlow_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.SequentiallyLocatedRealUp
