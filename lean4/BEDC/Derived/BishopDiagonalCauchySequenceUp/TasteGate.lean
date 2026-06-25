import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopDiagonalCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopDiagonalCauchySequenceUp : Type where
  | mk (F I S T R E H C P N : BHist) : BishopDiagonalCauchySequenceUp
  deriving DecidableEq

def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fields :
    BishopDiagonalCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopDiagonalCauchySequenceUp.mk F I S T R E H C P N =>
      [F, I, S, T, R, E, H, C, P, N]

def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist h

def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow :
    BishopDiagonalCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopDiagonalCauchySequenceUp.mk F I S T R E H C P N =>
      [BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist F,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist I,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist S,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist T,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist R,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist E,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist H,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist C,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist P,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist N]

private def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault index rest

def BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BishopDiagonalCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopDiagonalCauchySequenceUp.mk
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopDiagonalCauchySequenceUp,
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow x) =
          some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I S T R E H C P N =>
      change
        some
          (BishopDiagonalCauchySequenceUp.mk
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist F))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist I))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist S))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist T))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist R))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist E))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist H))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist C))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist P))
            (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
              (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BishopDiagonalCauchySequenceUp.mk F I S T R E H C P N)
      rw [BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode F,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode I,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode S,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode T,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode R,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode E,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode H,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode C,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode P,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopDiagonalCauchySequenceUp} :
    BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow x =
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow
          (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow
          (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_round_trip y)))

instance BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BishopDiagonalCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow

instance BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BishopDiagonalCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fromEventFlow
        (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment :
    (∀ F I S T R E H C P N : BHist,
      BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_fields
        (BishopDiagonalCauchySequenceUp.mk F I S T R E H C P N) =
          [F, I, S, T, R, E, H, C, P, N]) ∧
      (∀ h : BHist,
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decodeBHist
          (BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro F I S T R E H C P N
    rfl
  · constructor
    · exact BishopDiagonalCauchySequenceTasteGate_single_carrier_alignment_decode_encode
    · rfl

end BEDC.Derived.BishopDiagonalCauchySequenceUp
