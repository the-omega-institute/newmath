import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricBaireSurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricBaireSurfaceUp : Type where
  | mk :
      (baire completeMetric metric stream regular real transport replay provenance name : BHist) →
        CompleteMetricBaireSurfaceUp

def CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b0, BMark.b1]

def CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist h

def CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
          (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist h) =
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

def CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow :
    CompleteMetricBaireSurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricBaireSurfaceUp.mk baire completeMetric metric stream regular real transport
      replay provenance name =>
      [CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_tag,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist baire,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist completeMetric,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist metric,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist stream,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist regular,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist real,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist transport,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist replay,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist provenance,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist name]

def CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CompleteMetricBaireSurfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | baire :: rest1 =>
          match rest1 with
          | [] => none
          | completeMetric :: rest2 =>
              match rest2 with
              | [] => none
              | metric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | stream :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regular :: rest5 =>
                          match rest5 with
                          | [] => none
                          | real :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompleteMetricBaireSurfaceUp.mk
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        baire)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        completeMetric)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        metric)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        stream)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        regular)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        real)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        transport)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        replay)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        provenance)
                                                      (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
                                                        name))
                                              | _ :: _ => none

private theorem CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompleteMetricBaireSurfaceUp,
      CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow
          (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk baire completeMetric metric stream regular real transport replay provenance name =>
      change
        some
          (CompleteMetricBaireSurfaceUp.mk
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist baire))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist
                completeMetric))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist metric))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist stream))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist regular))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist real))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist
                transport))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist replay))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist
                provenance))
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
              (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist name))) =
          some
            (CompleteMetricBaireSurfaceUp.mk baire completeMetric metric stream regular real
              transport replay provenance name)
      rw [CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode baire,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode completeMetric,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode metric,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode stream,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode regular,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode real,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode transport,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode replay,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode provenance,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode name]

private theorem CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_injective
    {x y : CompleteMetricBaireSurfaceUp} :
    CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x =
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow
          (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow
          (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_round_trip y)))

instance CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CompleteMetricBaireSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow

instance CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompleteMetricBaireSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow
          (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_injective heq)

theorem CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decodeBHist
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      (∀ x : CompleteMetricBaireSurfaceUp,
        CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_fromEventFlow
            (CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
        (∀ x y : CompleteMetricBaireSurfaceUp,
          CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow x =
              CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_toEventFlow y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_round_trip
    · intro x y heq
      exact CompleteMetricBaireSurfaceTasteGate_single_carrier_alignment_injective heq

end BEDC.Derived.CompleteMetricBaireSurfaceUp
