import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelDirichletTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelDirichletTestUp : Type where
  | mk (S A B D Q R E H C P N : BHist) : AbelDirichletTestUp
  deriving DecidableEq

private def AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist h

private def AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def AbelDirichletTestTasteGate_single_carrier_alignment_fields :
    AbelDirichletTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelDirichletTestUp.mk S A B D Q R E H C P N => [S, A, B, D, Q, R, E, H, C, P, N]

private def AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow :
    AbelDirichletTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (AbelDirichletTestTasteGate_single_carrier_alignment_fields x).map
        AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist

private def AbelDirichletTestTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AbelDirichletTestTasteGate_single_carrier_alignment_eventAt index rest

private def AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option AbelDirichletTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelDirichletTestUp.mk
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 0 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 1 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 2 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 3 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 4 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 5 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 6 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 7 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 8 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 9 ef))
      (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (AbelDirichletTestTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem AbelDirichletTestTasteGate_single_carrier_alignment_round_trip
    (x : AbelDirichletTestUp) :
    AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow
      (AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A B D Q R E H C P N =>
      change
        some
          (AbelDirichletTestUp.mk
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist S))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist A))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist B))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist D))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist Q))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist R))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist E))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist H))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist C))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist P))
            (AbelDirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (AbelDirichletTestTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (AbelDirichletTestUp.mk S A B D Q R E H C P N)
      rw [AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode S,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode A,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode B,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode D,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode Q,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode R,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode E,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode H,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode C,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode P,
        AbelDirichletTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelDirichletTestUp} :
    AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow x =
      AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow
          (AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow x) =
        AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow
          (AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelDirichletTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelDirichletTestTasteGate_single_carrier_alignment_round_trip y)))

instance abelDirichletTestBHistCarrier : BHistCarrier AbelDirichletTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow

instance abelDirichletTestChapterTasteGate :
    ChapterTasteGate AbelDirichletTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      AbelDirichletTestTasteGate_single_carrier_alignment_fromEventFlow
        (AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact AbelDirichletTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelDirichletTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AbelDirichletTestTasteGate_single_carrier_alignment :
    ChapterTasteGate AbelDirichletTestUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact abelDirichletTestChapterTasteGate

end BEDC.Derived.AbelDirichletTestUp
