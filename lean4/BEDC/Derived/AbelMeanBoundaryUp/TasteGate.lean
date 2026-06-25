import BEDC.Derived.AbelMeanBoundaryUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelMeanBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist h

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_fields :
    AbelMeanBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelMeanBoundaryUp.mk S A T U W D R E H C P N => [S, A, T, U, W, D, R, E, H, C, P, N]

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow :
    AbelMeanBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_fields x).map
        AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt index rest

private def AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option AbelMeanBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelMeanBoundaryUp.mk
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 0 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 1 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 2 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 3 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 4 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 5 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 6 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 7 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 8 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 9 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 10 ef))
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem AbelMeanBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : AbelMeanBoundaryUp) :
    AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow
      (AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A T U W D R E H C P N =>
      change
        some
          (AbelMeanBoundaryUp.mk
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist S))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist A))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist T))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist U))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist W))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist D))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist R))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist E))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist H))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist C))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist P))
            (AbelMeanBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (AbelMeanBoundaryTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (AbelMeanBoundaryUp.mk S A T U W D R E H C P N)
      rw [AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode A,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode T,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode U,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode W,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        AbelMeanBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelMeanBoundaryUp} :
    AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow x =
      AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelMeanBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelMeanBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance abelMeanBoundaryBHistCarrier : BHistCarrier AbelMeanBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow

instance abelMeanBoundaryChapterTasteGate :
    ChapterTasteGate AbelMeanBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      AbelMeanBoundaryTasteGate_single_carrier_alignment_fromEventFlow
        (AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact AbelMeanBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelMeanBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AbelMeanBoundaryTasteGate_single_carrier_alignment :
    ChapterTasteGate AbelMeanBoundaryUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact abelMeanBoundaryChapterTasteGate

end BEDC.Derived.AbelMeanBoundaryUp
