import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionIdempotenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionIdempotenceUp : Type where
  | mk (M S C U R H K P N : BHist) : MetricCompletionIdempotenceUp
  deriving DecidableEq

def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist h

def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fields :
    MetricCompletionIdempotenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionIdempotenceUp.mk M S C U R H K P N => [M, S, C, U, R, H, K, P, N]

def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow :
    MetricCompletionIdempotenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fields token).map MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist

private def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt index rest

private def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest =>
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_lengthEq n rest

def MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MetricCompletionIdempotenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match MetricCompletionIdempotenceTasteGate_single_carrier_alignment_lengthEq 9 flow with
      | true =>
          some
            (MetricCompletionIdempotenceUp.mk
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 0 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 1 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 2 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 3 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 4 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 5 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 6 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 7 flow))
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
                (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_rawAt 8 flow)))
      | false => none

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip :
    ∀ token : MetricCompletionIdempotenceUp,
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow token) =
        some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M S C U R H K P N =>
      change
        some
          (MetricCompletionIdempotenceUp.mk
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist M))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist S))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist C))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist U))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist R))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist H))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist K))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist P))
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
              (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (MetricCompletionIdempotenceUp.mk M S C U R H K P N)
      rw [MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode U,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode K,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionIdempotenceUp} :
    MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow x =
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow x) =
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionIdempotenceBHistCarrier :
    BHistCarrier MetricCompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow

instance metricCompletionIdempotenceChapterTasteGate :
    ChapterTasteGate MetricCompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decodeBHist
          (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      (∀ x : MetricCompletionIdempotenceUp,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_fromEventFlow
            (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_encodeBHist
        BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode_encode,
      MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.MetricCompletionIdempotenceUp.TasteGate
