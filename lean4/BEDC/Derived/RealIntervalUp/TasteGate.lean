import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalUp : Type where
  | mk (L U E D W R S H C P N : BHist) : RealIntervalUp

def realIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalEncodeBHist h

def realIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalDecodeBHist tail)

private theorem RealIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realIntervalDecodeBHist (realIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalFields : RealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalUp.mk L U E D W R S H C P N => [L, U, E, D, W, R, S, H, C, P, N]

def realIntervalToEventFlow : RealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realIntervalFields x).map realIntervalEncodeBHist

private def realIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalEventAtDefault index rest

def realIntervalFromEventFlow (ef : EventFlow) : Option RealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalUp.mk
      (realIntervalDecodeBHist (realIntervalEventAtDefault 0 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 1 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 2 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 3 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 4 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 5 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 6 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 7 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 8 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 9 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 10 ef)))

private theorem RealIntervalTasteGate_single_carrier_alignment_round_trip
    (x : RealIntervalUp) :
    realIntervalFromEventFlow (realIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U E D W R S H C P N =>
      change
        some
          (RealIntervalUp.mk
            (realIntervalDecodeBHist (realIntervalEncodeBHist L))
            (realIntervalDecodeBHist (realIntervalEncodeBHist U))
            (realIntervalDecodeBHist (realIntervalEncodeBHist E))
            (realIntervalDecodeBHist (realIntervalEncodeBHist D))
            (realIntervalDecodeBHist (realIntervalEncodeBHist W))
            (realIntervalDecodeBHist (realIntervalEncodeBHist R))
            (realIntervalDecodeBHist (realIntervalEncodeBHist S))
            (realIntervalDecodeBHist (realIntervalEncodeBHist H))
            (realIntervalDecodeBHist (realIntervalEncodeBHist C))
            (realIntervalDecodeBHist (realIntervalEncodeBHist P))
            (realIntervalDecodeBHist (realIntervalEncodeBHist N))) =
          some (RealIntervalUp.mk L U E D W R S H C P N)
      rw [RealIntervalTasteGate_single_carrier_alignment_decode_encode L,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode U,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode E,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode D,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode W,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode R,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode S,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode H,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode C,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode P,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealIntervalTasteGate_single_carrier_alignment_injective
    {x y : RealIntervalUp} :
    realIntervalToEventFlow x = realIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalFromEventFlow (realIntervalToEventFlow x) =
        realIntervalFromEventFlow (realIntervalToEventFlow y) :=
    congrArg realIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance realIntervalBHistCarrier : BHistCarrier RealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalToEventFlow
  fromEventFlow := realIntervalFromEventFlow

instance realIntervalChapterTasteGate : ChapterTasteGate RealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalFromEventFlow (realIntervalToEventFlow x) = some x
    exact RealIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntervalTasteGate_single_carrier_alignment_injective heq)

theorem RealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, realIntervalDecodeBHist (realIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealIntervalUp) ∧
        Nonempty (ChapterTasteGate RealIntervalUp) ∧
          realIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealIntervalTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨realIntervalBHistCarrier⟩
    · constructor
      · exact ⟨realIntervalChapterTasteGate⟩
      · rfl

end BEDC.Derived.RealIntervalUp
