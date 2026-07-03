import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMonotoneSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealMonotoneSequenceUp : Type where
  | mk (S M W Q E H C P N : BHist) : RealMonotoneSequenceUp
  deriving DecidableEq

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist h

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_fields :
    RealMonotoneSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealMonotoneSequenceUp.mk S M W Q E H C P N => [S, M, W, Q, E, H, C, P, N]

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow :
    RealMonotoneSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_fields x).map
        RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt index rest

private def RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option RealMonotoneSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealMonotoneSequenceUp.mk
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem RealMonotoneSequenceTasteGate_single_carrier_alignment_round_trip
    (x : RealMonotoneSequenceUp) :
    RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow
      (RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M W Q E H C P N =>
      change
        some
          (RealMonotoneSequenceUp.mk
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist S))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist M))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist W))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist Q))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist E))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist H))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist C))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist P))
            (RealMonotoneSequenceTasteGate_single_carrier_alignment_decodeBHist
              (RealMonotoneSequenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RealMonotoneSequenceUp.mk S M W Q E H C P N)
      rw [RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode S,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode M,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode W,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode Q,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode E,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode H,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode C,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode P,
        RealMonotoneSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealMonotoneSequenceUp} :
    RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow x =
      RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealMonotoneSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealMonotoneSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance realMonotoneSequenceBHistCarrier : BHistCarrier RealMonotoneSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow

instance realMonotoneSequenceChapterTasteGate :
    ChapterTasteGate RealMonotoneSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealMonotoneSequenceTasteGate_single_carrier_alignment_fromEventFlow
        (RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact RealMonotoneSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealMonotoneSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealMonotoneSequenceTasteGate_single_carrier_alignment :
    Nonempty RealMonotoneSequenceUp ∧
      ∃ carrierInst : BHistCarrier RealMonotoneSequenceUp,
        @ChapterTasteGate RealMonotoneSequenceUp carrierInst := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨RealMonotoneSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty
    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩,
    ⟨realMonotoneSequenceBHistCarrier, realMonotoneSequenceChapterTasteGate⟩⟩

end BEDC.Derived.RealMonotoneSequenceUp.TasteGate
