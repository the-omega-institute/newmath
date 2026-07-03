import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletTestUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletTestUp : Type where
  | mk (S A B T R E H C P N : BHist) : DirichletTestUp
  deriving DecidableEq

private def DirichletTestTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DirichletTestTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DirichletTestTasteGate_single_carrier_alignment_encodeBHist h

private def DirichletTestTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (DirichletTestTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (DirichletTestTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DirichletTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def DirichletTestTasteGate_single_carrier_alignment_fields :
    DirichletTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletTestUp.mk S A B T R E H C P N => [S, A, B, T, R, E, H, C, P, N]

private def DirichletTestTasteGate_single_carrier_alignment_toEventFlow :
    DirichletTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (DirichletTestTasteGate_single_carrier_alignment_fields x).map
        DirichletTestTasteGate_single_carrier_alignment_encodeBHist

private def DirichletTestTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DirichletTestTasteGate_single_carrier_alignment_eventAt index rest

private def DirichletTestTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option DirichletTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DirichletTestUp.mk
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 0 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 1 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 2 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 3 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 4 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 5 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 6 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 7 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 8 ef))
      (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
        (DirichletTestTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem DirichletTestTasteGate_single_carrier_alignment_round_trip
    (x : DirichletTestUp) :
    DirichletTestTasteGate_single_carrier_alignment_fromEventFlow
      (DirichletTestTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A B T R E H C P N =>
      change
        some
          (DirichletTestUp.mk
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist S))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist A))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist B))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist T))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist R))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist E))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist H))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist C))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist P))
            (DirichletTestTasteGate_single_carrier_alignment_decodeBHist
              (DirichletTestTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (DirichletTestUp.mk S A B T R E H C P N)
      rw [DirichletTestTasteGate_single_carrier_alignment_decode_encode S,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode A,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode B,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode T,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode R,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode E,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode H,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode C,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode P,
        DirichletTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem DirichletTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DirichletTestUp} :
    DirichletTestTasteGate_single_carrier_alignment_toEventFlow x =
      DirichletTestTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DirichletTestTasteGate_single_carrier_alignment_fromEventFlow
          (DirichletTestTasteGate_single_carrier_alignment_toEventFlow x) =
        DirichletTestTasteGate_single_carrier_alignment_fromEventFlow
          (DirichletTestTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DirichletTestTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DirichletTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DirichletTestTasteGate_single_carrier_alignment_round_trip y)))

instance dirichletTestBHistCarrier : BHistCarrier DirichletTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DirichletTestTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DirichletTestTasteGate_single_carrier_alignment_fromEventFlow

instance dirichletTestChapterTasteGate :
    ChapterTasteGate DirichletTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DirichletTestTasteGate_single_carrier_alignment_fromEventFlow
        (DirichletTestTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact DirichletTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DirichletTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DirichletTestTasteGate_single_carrier_alignment :
    Nonempty DirichletTestUp ∧
      ∃ carrierInst : BHistCarrier DirichletTestUp,
        @ChapterTasteGate DirichletTestUp carrierInst := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨DirichletTestUp.mk BHist.Empty BHist.Empty BHist.Empty
    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩,
    ⟨dirichletTestBHistCarrier, dirichletTestChapterTasteGate⟩⟩

end BEDC.Derived.DirichletTestUp.TasteGate
