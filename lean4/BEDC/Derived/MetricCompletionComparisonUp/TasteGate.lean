import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionComparisonUp : Type where
  | mk (U D E0 E1 S R W Q A H C P N : BHist) : MetricCompletionComparisonUp
  deriving DecidableEq

def metricCompletionComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionComparisonEncodeBHist h

def metricCompletionComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionComparisonDecodeBHist tail)

private theorem MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionComparisonDecodeBHist (metricCompletionComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionComparisonToEventFlow : MetricCompletionComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionComparisonUp.mk U D E0 E1 S R W Q A H C P N =>
      [metricCompletionComparisonEncodeBHist U, metricCompletionComparisonEncodeBHist D,
        metricCompletionComparisonEncodeBHist E0, metricCompletionComparisonEncodeBHist E1,
        metricCompletionComparisonEncodeBHist S, metricCompletionComparisonEncodeBHist R,
        metricCompletionComparisonEncodeBHist W, metricCompletionComparisonEncodeBHist Q,
        metricCompletionComparisonEncodeBHist A, metricCompletionComparisonEncodeBHist H,
        metricCompletionComparisonEncodeBHist C, metricCompletionComparisonEncodeBHist P,
        metricCompletionComparisonEncodeBHist N]

def metricCompletionComparisonFromEventFlow (flow : EventFlow) :
    Option MetricCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | U :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | E0 :: rest2 =>
              match rest2 with
              | [] => none
              | E1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | W :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | A :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (MetricCompletionComparisonUp.mk
                                                              (metricCompletionComparisonDecodeBHist U)
                                                              (metricCompletionComparisonDecodeBHist D)
                                                              (metricCompletionComparisonDecodeBHist E0)
                                                              (metricCompletionComparisonDecodeBHist E1)
                                                              (metricCompletionComparisonDecodeBHist S)
                                                              (metricCompletionComparisonDecodeBHist R)
                                                              (metricCompletionComparisonDecodeBHist W)
                                                              (metricCompletionComparisonDecodeBHist Q)
                                                              (metricCompletionComparisonDecodeBHist A)
                                                              (metricCompletionComparisonDecodeBHist H)
                                                              (metricCompletionComparisonDecodeBHist C)
                                                              (metricCompletionComparisonDecodeBHist P)
                                                              (metricCompletionComparisonDecodeBHist N))
                                                      | _ :: _ => none

private theorem MetricCompletionComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionComparisonUp,
      metricCompletionComparisonFromEventFlow (metricCompletionComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U D E0 E1 S R W Q A H C P N =>
      change
        some
          (MetricCompletionComparisonUp.mk
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist U))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist D))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist E0))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist E1))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist S))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist R))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist W))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist Q))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist A))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist H))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist C))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist P))
            (metricCompletionComparisonDecodeBHist
              (metricCompletionComparisonEncodeBHist N))) =
          some (MetricCompletionComparisonUp.mk U D E0 E1 S R W Q A H C P N)
      rw [MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode U,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode D,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode E0,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode E1,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode W,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode Q,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode A,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionComparisonUp} :
    metricCompletionComparisonToEventFlow x =
      metricCompletionComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionComparisonFromEventFlow (metricCompletionComparisonToEventFlow x) =
        metricCompletionComparisonFromEventFlow (metricCompletionComparisonToEventFlow y) :=
    congrArg metricCompletionComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionComparisonBHistCarrier : BHistCarrier MetricCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionComparisonToEventFlow
  fromEventFlow := metricCompletionComparisonFromEventFlow

instance metricCompletionComparisonChapterTasteGate :
    ChapterTasteGate MetricCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionComparisonFromEventFlow
      (metricCompletionComparisonToEventFlow x) = some x
    exact MetricCompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionComparisonChapterTasteGate

theorem MetricCompletionComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionComparisonDecodeBHist (metricCompletionComparisonEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionComparisonUp,
        metricCompletionComparisonFromEventFlow
          (metricCompletionComparisonToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionComparisonUp,
          metricCompletionComparisonToEventFlow x =
            metricCompletionComparisonToEventFlow y → x = y) ∧
          metricCompletionComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetricCompletionComparisonTasteGate_single_carrier_alignment_decode_encode,
      MetricCompletionComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetricCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionComparisonUp
