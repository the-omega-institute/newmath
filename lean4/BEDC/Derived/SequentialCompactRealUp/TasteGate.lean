import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCompactRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCompactRealUp : Type where
  | mk (A W Q I S E H C P N : BHist) : SequentialCompactRealUp
  deriving DecidableEq

def sequentialCompactRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCompactRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCompactRealEncodeBHist h

def sequentialCompactRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCompactRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCompactRealDecodeBHist tail)

private theorem SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialCompactRealFields : SequentialCompactRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompactRealUp.mk A W Q I S E H C P N => [A, W, Q, I, S, E, H, C, P, N]

def sequentialCompactRealToEventFlow : SequentialCompactRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialCompactRealFields x).map sequentialCompactRealEncodeBHist

private def sequentialCompactRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialCompactRealEventAt index rest

def sequentialCompactRealFromEventFlow (ef : EventFlow) : Option SequentialCompactRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialCompactRealUp.mk
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 0 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 1 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 2 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 3 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 4 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 5 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 6 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 7 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 8 ef))
      (sequentialCompactRealDecodeBHist (sequentialCompactRealEventAt 9 ef)))

private theorem SequentialCompactRealTasteGate_single_carrier_alignment_round_trip
    (x : SequentialCompactRealUp) :
    sequentialCompactRealFromEventFlow (sequentialCompactRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A W Q I S E H C P N =>
      change
        some
          (SequentialCompactRealUp.mk
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist A))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist W))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist Q))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist I))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist S))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist E))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist H))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist C))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist P))
            (sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist N))) =
          some (SequentialCompactRealUp.mk A W Q I S E H C P N)
      rw [SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode A,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode W,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode Q,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode I,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode S,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode E,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode H,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode C,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode P,
        SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem SequentialCompactRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialCompactRealUp} :
    sequentialCompactRealToEventFlow x = sequentialCompactRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCompactRealFromEventFlow (sequentialCompactRealToEventFlow x) =
        sequentialCompactRealFromEventFlow (sequentialCompactRealToEventFlow y) :=
    congrArg sequentialCompactRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialCompactRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SequentialCompactRealTasteGate_single_carrier_alignment_round_trip y)))

instance sequentialCompactRealBHistCarrier : BHistCarrier SequentialCompactRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCompactRealToEventFlow
  fromEventFlow := sequentialCompactRealFromEventFlow

instance sequentialCompactRealChapterTasteGate : ChapterTasteGate SequentialCompactRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCompactRealFromEventFlow (sequentialCompactRealToEventFlow x) = some x
    exact SequentialCompactRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentialCompactRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SequentialCompactRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialCompactRealDecodeBHist (sequentialCompactRealEncodeBHist h) = h) ∧
      sequentialCompactRealFromEventFlow
          (sequentialCompactRealToEventFlow
            (SequentialCompactRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
        some
          (SequentialCompactRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SequentialCompactRealTasteGate_single_carrier_alignment_decode_encode,
      SequentialCompactRealTasteGate_single_carrier_alignment_round_trip
        (SequentialCompactRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)⟩

end BEDC.Derived.SequentialCompactRealUp
