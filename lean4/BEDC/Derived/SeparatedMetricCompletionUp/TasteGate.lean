import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedMetricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedMetricCompletionUp : Type where
  | mk (M B Q R Z H C P N : BHist) : SeparatedMetricCompletionUp
  deriving DecidableEq

def separatedMetricCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedMetricCompletionEncodeBHist h

def separatedMetricCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedMetricCompletionDecodeBHist tail)

private theorem SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      separatedMetricCompletionDecodeBHist
          (separatedMetricCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedMetricCompletionToEventFlow :
    SeparatedMetricCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedMetricCompletionUp.mk M B Q R Z H C P N =>
      [separatedMetricCompletionEncodeBHist M,
        separatedMetricCompletionEncodeBHist B,
        separatedMetricCompletionEncodeBHist Q,
        separatedMetricCompletionEncodeBHist R,
        separatedMetricCompletionEncodeBHist Z,
        separatedMetricCompletionEncodeBHist H,
        separatedMetricCompletionEncodeBHist C,
        separatedMetricCompletionEncodeBHist P,
        separatedMetricCompletionEncodeBHist N]

private def separatedMetricCompletionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedMetricCompletionEventAt index rest

def separatedMetricCompletionDecodeFields (ef : EventFlow) :
    SeparatedMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SeparatedMetricCompletionUp.mk
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 0 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 1 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 2 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 3 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 4 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 5 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 6 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 7 ef))
    (separatedMetricCompletionDecodeBHist (separatedMetricCompletionEventAt 8 ef))

def separatedMetricCompletionFromEventFlow :
    EventFlow -> Option SeparatedMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (separatedMetricCompletionDecodeFields ef)

private theorem SeparatedMetricCompletionTasteGate_single_carrier_alignment_round_trip
    (x : SeparatedMetricCompletionUp) :
    separatedMetricCompletionFromEventFlow
        (separatedMetricCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B Q R Z H C P N =>
      change
        some
            (SeparatedMetricCompletionUp.mk
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist M))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist B))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist Q))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist R))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist Z))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist H))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist C))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist P))
              (separatedMetricCompletionDecodeBHist
                (separatedMetricCompletionEncodeBHist N))) =
          some (SeparatedMetricCompletionUp.mk M B Q R Z H C P N)
      rw [SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode M,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode B,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode R,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode Z,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode H,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode C,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode P,
        SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem SeparatedMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedMetricCompletionUp} :
    separatedMetricCompletionToEventFlow x =
        separatedMetricCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedMetricCompletionFromEventFlow
          (separatedMetricCompletionToEventFlow x) =
        separatedMetricCompletionFromEventFlow
          (separatedMetricCompletionToEventFlow y) :=
    congrArg separatedMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance separatedMetricCompletionBHistCarrier :
    BHistCarrier SeparatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedMetricCompletionToEventFlow
  fromEventFlow := separatedMetricCompletionFromEventFlow

instance separatedMetricCompletionChapterTasteGate :
    ChapterTasteGate SeparatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedMetricCompletionFromEventFlow
          (separatedMetricCompletionToEventFlow x) =
        some x
    exact SeparatedMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SeparatedMetricCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      separatedMetricCompletionDecodeBHist
          (separatedMetricCompletionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier SeparatedMetricCompletionUp) ∧
        Nonempty (ChapterTasteGate SeparatedMetricCompletionUp) ∧
          separatedMetricCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SeparatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨separatedMetricCompletionBHistCarrier⟩,
      ⟨separatedMetricCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SeparatedMetricCompletionUp
