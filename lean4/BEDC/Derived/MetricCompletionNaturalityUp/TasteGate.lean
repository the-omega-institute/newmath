import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# MetricCompletionNaturalityUp TasteGate carrier.
-/

namespace BEDC.Derived.MetricCompletionNaturalityUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Metric-completion naturality packet with the eleven displayed rows. -/
inductive MetricCompletionNaturalityUp : Type where
  | mk : (M_X M_Y F E S R A H C P L : BHist) → MetricCompletionNaturalityUp
  deriving DecidableEq

def metricCompletionNaturalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionNaturalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionNaturalityEncodeBHist h

def metricCompletionNaturalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionNaturalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionNaturalityDecodeBHist tail)

private theorem MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionNaturalityDecodeBHist
        (metricCompletionNaturalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionNaturalityToEventFlow : MetricCompletionNaturalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionNaturalityUp.mk M_X M_Y F E S R A H C P L =>
      [[BMark.b0],
        metricCompletionNaturalityEncodeBHist M_X,
        [BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist M_Y,
        [BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metricCompletionNaturalityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionNaturalityEncodeBHist L]

private def metricCompletionNaturalityDecodeRows :
    EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match metricCompletionNaturalityDecodeRows rest1 with
          | some rows => some (metricCompletionNaturalityDecodeBHist row :: rows)
          | none => none

private def metricCompletionNaturalityFromRows :
    List BHist → Option MetricCompletionNaturalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M_X :: rest0 =>
      match rest0 with
      | [] => none
      | M_Y :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
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
                                          | L :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (MetricCompletionNaturalityUp.mk
                                                      M_X M_Y F E S R A H C P L)
                                              | _ :: _ => none

def metricCompletionNaturalityFromEventFlow :
    EventFlow → Option MetricCompletionNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match metricCompletionNaturalityDecodeRows ef with
    | some rows => metricCompletionNaturalityFromRows rows
    | none => none

private theorem MetricCompletionNaturalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionNaturalityUp,
      metricCompletionNaturalityFromEventFlow
        (metricCompletionNaturalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M_X M_Y F E S R A H C P L =>
      change
        some
          (MetricCompletionNaturalityUp.mk
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist M_X))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist M_Y))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist F))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist E))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist S))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist R))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist A))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist H))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist C))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist P))
            (metricCompletionNaturalityDecodeBHist
              (metricCompletionNaturalityEncodeBHist L))) =
          some (MetricCompletionNaturalityUp.mk M_X M_Y F E S R A H C P L)
      rw [MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode M_X,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode M_Y,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode F,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode E,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode A,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode L]

private theorem MetricCompletionNaturalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionNaturalityUp} :
    metricCompletionNaturalityToEventFlow x =
      metricCompletionNaturalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionNaturalityFromEventFlow
          (metricCompletionNaturalityToEventFlow x) =
        metricCompletionNaturalityFromEventFlow
          (metricCompletionNaturalityToEventFlow y) :=
    congrArg metricCompletionNaturalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionNaturalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionNaturalityTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionNaturalityBHistCarrier :
    BHistCarrier MetricCompletionNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionNaturalityToEventFlow
  fromEventFlow := metricCompletionNaturalityFromEventFlow

instance metricCompletionNaturalityChapterTasteGate :
    ChapterTasteGate MetricCompletionNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionNaturalityFromEventFlow
        (metricCompletionNaturalityToEventFlow x) = some x
    exact MetricCompletionNaturalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionNaturalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the metric-completion naturality carrier. -/
def taste_gate : ChapterTasteGate MetricCompletionNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionNaturalityChapterTasteGate

theorem MetricCompletionNaturalityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metricCompletionNaturalityDecodeBHist
          (metricCompletionNaturalityEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionNaturalityUp,
        metricCompletionNaturalityFromEventFlow
          (metricCompletionNaturalityToEventFlow x) = some x) ∧
      (∀ x y : MetricCompletionNaturalityUp,
        metricCompletionNaturalityToEventFlow x =
          metricCompletionNaturalityToEventFlow y → x = y) ∧
      metricCompletionNaturalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetricCompletionNaturalityTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetricCompletionNaturalityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          MetricCompletionNaturalityTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.MetricCompletionNaturalityUp
