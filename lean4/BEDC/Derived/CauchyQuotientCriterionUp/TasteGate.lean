import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyQuotientCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyQuotientCriterionUp : Type where
  | mk (A B Z W D P K R E H C L N : BHist) : CauchyQuotientCriterionUp

private def CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist h

private def CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow :
    CauchyQuotientCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyQuotientCriterionUp.mk A B Z W D P K R E H C L N =>
      [CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist A,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist B,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist Z,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist W,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist D,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist P,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist K,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist R,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist E,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist H,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist C,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist L,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist N]

private def CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt index rest

private def CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CauchyQuotientCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyQuotientCriterionUp.mk
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 9 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 10 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 11 ef))
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem CauchyQuotientCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyQuotientCriterionUp,
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B Z W D P K R E H C L N =>
      change
        some
          (CauchyQuotientCriterionUp.mk
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist A))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist B))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist Z))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist W))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist K))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist L))
            (CauchyQuotientCriterionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyQuotientCriterionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyQuotientCriterionUp.mk A B Z W D P K R E H C L N)
      rw [CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode A,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode B,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode K,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode L,
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyQuotientCriterionUp} :
    CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyQuotientCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyQuotientCriterionBHistCarrier :
    BHistCarrier CauchyQuotientCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyQuotientCriterionChapterTasteGate :
    ChapterTasteGate CauchyQuotientCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyQuotientCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyQuotientCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyQuotientCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyQuotientCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyQuotientCriterionChapterTasteGate

theorem CauchyQuotientCriterionTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyQuotientCriterionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact cauchyQuotientCriterionChapterTasteGate

end BEDC.Derived.CauchyQuotientCriterionUp
