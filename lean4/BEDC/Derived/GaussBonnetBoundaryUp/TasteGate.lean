import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaussBonnetBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaussBonnetBoundaryUp : Type where
  | mk (S M K B F D E H C P N : BHist) : GaussBonnetBoundaryUp

private def GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist h

private def GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow :
    GaussBonnetBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GaussBonnetBoundaryUp.mk S M K B F D E H C P N =>
      [GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist S,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist M,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist K,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist B,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist F,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist D,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist E,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist H,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist C,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist P,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist N]

private def GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt index rest

private def GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option GaussBonnetBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GaussBonnetBoundaryUp.mk
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 0 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 1 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 2 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 3 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 4 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 5 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 6 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 7 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 8 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 9 ef))
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (GaussBonnetBoundaryTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem GaussBonnetBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GaussBonnetBoundaryUp,
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M K B F D E H C P N =>
      change
        some
          (GaussBonnetBoundaryUp.mk
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist S))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist M))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist K))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist B))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist F))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist D))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist E))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist H))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist C))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist P))
            (GaussBonnetBoundaryTasteGate_single_carrier_alignment_decodeBHist
              (GaussBonnetBoundaryTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (GaussBonnetBoundaryUp.mk S M K B F D E H C P N)
      rw [GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode M,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode K,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode B,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode F,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GaussBonnetBoundaryUp} :
    GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow x =
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GaussBonnetBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GaussBonnetBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance gaussBonnetBoundaryBHistCarrier : BHistCarrier GaussBonnetBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow

instance gaussBonnetBoundaryChapterTasteGate : ChapterTasteGate GaussBonnetBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      GaussBonnetBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact GaussBonnetBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaussBonnetBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate GaussBonnetBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gaussBonnetBoundaryChapterTasteGate

theorem GaussBonnetBoundaryTasteGate_single_carrier_alignment :
    ChapterTasteGate GaussBonnetBoundaryUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact gaussBonnetBoundaryChapterTasteGate

end BEDC.Derived.GaussBonnetBoundaryUp
