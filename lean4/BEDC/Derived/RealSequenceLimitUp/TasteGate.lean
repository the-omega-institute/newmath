import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceLimitUp : Type where
  | mk :
      (sequence limit window tolerance classifier transport continuation provenance
        nameCert : BHist) →
      RealSequenceLimitUp
  deriving DecidableEq

def realSequenceLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequenceLimitEncodeBHist h

def realSequenceLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequenceLimitDecodeBHist tail)

private theorem RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSequenceLimitToEventFlow : RealSequenceLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceLimitUp.mk sequence limit window tolerance classifier transport
      continuation provenance nameCert =>
      [[BMark.b0],
        realSequenceLimitEncodeBHist sequence,
        [BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist limit,
        [BMark.b1, BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realSequenceLimitEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realSequenceLimitEncodeBHist nameCert]

def realSequenceLimitFromEventFlow : EventFlow → Option RealSequenceLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sequence :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | limit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tolerance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | classifier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RealSequenceLimitUp.mk
                                                                                  (realSequenceLimitDecodeBHist sequence)
                                                                                  (realSequenceLimitDecodeBHist limit)
                                                                                  (realSequenceLimitDecodeBHist window)
                                                                                  (realSequenceLimitDecodeBHist tolerance)
                                                                                  (realSequenceLimitDecodeBHist classifier)
                                                                                  (realSequenceLimitDecodeBHist transport)
                                                                                  (realSequenceLimitDecodeBHist continuation)
                                                                                  (realSequenceLimitDecodeBHist provenance)
                                                                                  (realSequenceLimitDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem realSequenceLimit_round_trip :
    ∀ x : RealSequenceLimitUp,
      realSequenceLimitFromEventFlow (realSequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sequence limit window tolerance classifier transport continuation provenance nameCert =>
      change
        some
          (RealSequenceLimitUp.mk
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist sequence))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist limit))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist window))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist tolerance))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist classifier))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist transport))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist continuation))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist provenance))
            (realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist nameCert))) =
          some
            (RealSequenceLimitUp.mk sequence limit window tolerance classifier transport
              continuation provenance nameCert)
      have hSequence :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode sequence
      have hLimit :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode limit
      have hWindow :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode window
      have hTolerance :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode tolerance
      have hClassifier :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode classifier
      have hTransport :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode transport
      have hContinuation :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode continuation
      have hProvenance :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode provenance
      have hNameCert :=
        RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode nameCert
      rw [hSequence, hLimit, hWindow, hTolerance, hClassifier, hTransport,
        hContinuation, hProvenance, hNameCert]

private theorem realSequenceLimitToEventFlow_injective {x y : RealSequenceLimitUp} :
    realSequenceLimitToEventFlow x = realSequenceLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequenceLimitFromEventFlow (realSequenceLimitToEventFlow x) =
        realSequenceLimitFromEventFlow (realSequenceLimitToEventFlow y) :=
    congrArg realSequenceLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSequenceLimit_round_trip x).symm
      (Eq.trans hread (realSequenceLimit_round_trip y)))

instance realSequenceLimitBHistCarrier : BHistCarrier RealSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequenceLimitToEventFlow
  fromEventFlow := realSequenceLimitFromEventFlow

instance realSequenceLimitChapterTasteGate : ChapterTasteGate RealSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSequenceLimitFromEventFlow (realSequenceLimitToEventFlow x) = some x
    exact realSequenceLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSequenceLimitToEventFlow_injective heq)

theorem RealSequenceLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSequenceLimitDecodeBHist (realSequenceLimitEncodeBHist h) = h) ∧
      (∀ x : RealSequenceLimitUp,
        realSequenceLimitFromEventFlow (realSequenceLimitToEventFlow x) = some x) ∧
        (∀ x y : RealSequenceLimitUp,
          realSequenceLimitToEventFlow x = realSequenceLimitToEventFlow y → x = y) ∧
          realSequenceLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact realSequenceLimit_round_trip
    · constructor
      · intro x y heq
        exact realSequenceLimitToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSequenceLimitUp
