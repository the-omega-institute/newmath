import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionFiniteCoproductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionFiniteCoproductUp : Type where
  | mk (I S M W R A J H C P N : BHist) : MetricCompletionFiniteCoproductUp
  deriving DecidableEq

def metricCompletionFiniteCoproductEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionFiniteCoproductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionFiniteCoproductEncodeBHist h

def metricCompletionFiniteCoproductDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionFiniteCoproductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionFiniteCoproductDecodeBHist tail)

private theorem MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metricCompletionFiniteCoproductDecodeBHist
        (metricCompletionFiniteCoproductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricCompletionFiniteCoproductFields :
    MetricCompletionFiniteCoproductUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionFiniteCoproductUp.mk I S M W R A J H C P N =>
      [I, S, M, W, R, A, J, H, C, P, N]

def metricCompletionFiniteCoproductToEventFlow :
    MetricCompletionFiniteCoproductUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metricCompletionFiniteCoproductFields x).map
        metricCompletionFiniteCoproductEncodeBHist

def metricCompletionFiniteCoproductFromEventFlow :
    EventFlow -> Option MetricCompletionFiniteCoproductUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | J :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (MetricCompletionFiniteCoproductUp.mk
                                                      (metricCompletionFiniteCoproductDecodeBHist I)
                                                      (metricCompletionFiniteCoproductDecodeBHist S)
                                                      (metricCompletionFiniteCoproductDecodeBHist M)
                                                      (metricCompletionFiniteCoproductDecodeBHist W)
                                                      (metricCompletionFiniteCoproductDecodeBHist R)
                                                      (metricCompletionFiniteCoproductDecodeBHist A)
                                                      (metricCompletionFiniteCoproductDecodeBHist J)
                                                      (metricCompletionFiniteCoproductDecodeBHist H)
                                                      (metricCompletionFiniteCoproductDecodeBHist C)
                                                      (metricCompletionFiniteCoproductDecodeBHist P)
                                                      (metricCompletionFiniteCoproductDecodeBHist N))
                                              | _ :: _ => none

private theorem MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_round_trip :
    forall x : MetricCompletionFiniteCoproductUp,
      metricCompletionFiniteCoproductFromEventFlow
          (metricCompletionFiniteCoproductToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S M W R A J H C P N =>
      change
        some
          (MetricCompletionFiniteCoproductUp.mk
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist I))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist S))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist M))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist W))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist R))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist A))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist J))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist H))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist C))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist P))
            (metricCompletionFiniteCoproductDecodeBHist
              (metricCompletionFiniteCoproductEncodeBHist N))) =
          some (MetricCompletionFiniteCoproductUp.mk I S M W R A J H C P N)
      rw [MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode I,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode W,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode A,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode J,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_injective
    {x y : MetricCompletionFiniteCoproductUp} :
    metricCompletionFiniteCoproductToEventFlow x =
      metricCompletionFiniteCoproductToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionFiniteCoproductFromEventFlow
          (metricCompletionFiniteCoproductToEventFlow x) =
        metricCompletionFiniteCoproductFromEventFlow
          (metricCompletionFiniteCoproductToEventFlow y) :=
    congrArg metricCompletionFiniteCoproductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionFiniteCoproductBHistCarrier :
    BHistCarrier MetricCompletionFiniteCoproductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionFiniteCoproductToEventFlow
  fromEventFlow := metricCompletionFiniteCoproductFromEventFlow

instance metricCompletionFiniteCoproductChapterTasteGate :
    ChapterTasteGate MetricCompletionFiniteCoproductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionFiniteCoproductFromEventFlow
          (metricCompletionFiniteCoproductToEventFlow x) =
        some x
    exact MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetricCompletionFiniteCoproductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionFiniteCoproductChapterTasteGate

theorem MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metricCompletionFiniteCoproductDecodeBHist
        (metricCompletionFiniteCoproductEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricCompletionFiniteCoproductUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionFiniteCoproductUp) ∧
          metricCompletionFiniteCoproductEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact MetricCompletionFiniteCoproductTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨metricCompletionFiniteCoproductBHistCarrier⟩
    · constructor
      · exact ⟨metricCompletionFiniteCoproductChapterTasteGate⟩
      · rfl

end BEDC.Derived.MetricCompletionFiniteCoproductUp
