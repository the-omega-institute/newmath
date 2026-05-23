import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricUp : Type where
  | mk (metricCarrier stream modulus limit convergence stability ledger nameCert : BHist) :
      CompleteMetricUp

def CompleteMetricUpTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def completeMetricUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricUpEncodeBHist h

def completeMetricUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricUpDecodeBHist tail)

private theorem completeMetricUp_decode_encode_bhist :
    ∀ h : BHist, completeMetricUpDecodeBHist (completeMetricUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completeMetricUpToEventFlow : CompleteMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricUp.mk metricCarrier stream modulus limit convergence stability ledger nameCert =>
      [CompleteMetricUpTasteGate_single_carrier_alignment_tag,
        completeMetricUpEncodeBHist metricCarrier,
        completeMetricUpEncodeBHist stream,
        completeMetricUpEncodeBHist modulus,
        completeMetricUpEncodeBHist limit,
        completeMetricUpEncodeBHist convergence,
        completeMetricUpEncodeBHist stability,
        completeMetricUpEncodeBHist ledger,
        completeMetricUpEncodeBHist nameCert]

def completeMetricUpFromEventFlow : EventFlow → Option CompleteMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | metricCarrier :: rest1 =>
          match rest1 with
          | [] => none
          | stream :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | limit :: rest4 =>
                      match rest4 with
                      | [] => none
                      | convergence :: rest5 =>
                          match rest5 with
                          | [] => none
                          | stability :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CompleteMetricUp.mk
                                              (completeMetricUpDecodeBHist metricCarrier)
                                              (completeMetricUpDecodeBHist stream)
                                              (completeMetricUpDecodeBHist modulus)
                                              (completeMetricUpDecodeBHist limit)
                                              (completeMetricUpDecodeBHist convergence)
                                              (completeMetricUpDecodeBHist stability)
                                              (completeMetricUpDecodeBHist ledger)
                                              (completeMetricUpDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem completeMetricUp_round_trip :
    ∀ x : CompleteMetricUp,
      completeMetricUpFromEventFlow (completeMetricUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricCarrier stream modulus limit convergence stability ledger nameCert =>
      change
        some
          (CompleteMetricUp.mk
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist metricCarrier))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist stream))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist modulus))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist limit))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist convergence))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist stability))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist ledger))
            (completeMetricUpDecodeBHist (completeMetricUpEncodeBHist nameCert))) =
          some
            (CompleteMetricUp.mk metricCarrier stream modulus limit convergence stability ledger
              nameCert)
      rw [completeMetricUp_decode_encode_bhist metricCarrier,
        completeMetricUp_decode_encode_bhist stream,
        completeMetricUp_decode_encode_bhist modulus,
        completeMetricUp_decode_encode_bhist limit,
        completeMetricUp_decode_encode_bhist convergence,
        completeMetricUp_decode_encode_bhist stability,
        completeMetricUp_decode_encode_bhist ledger,
        completeMetricUp_decode_encode_bhist nameCert]

private theorem completeMetricUpToEventFlow_injective {x y : CompleteMetricUp} :
    completeMetricUpToEventFlow x = completeMetricUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricUpFromEventFlow (completeMetricUpToEventFlow x) =
        completeMetricUpFromEventFlow (completeMetricUpToEventFlow y) :=
    congrArg completeMetricUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeMetricUp_round_trip x).symm
      (Eq.trans hread (completeMetricUp_round_trip y)))

instance completeMetricUpBHistCarrier : BHistCarrier CompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricUpToEventFlow
  fromEventFlow := completeMetricUpFromEventFlow

instance completeMetricUpChapterTasteGate : ChapterTasteGate CompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeMetricUpFromEventFlow (completeMetricUpToEventFlow x) = some x
    exact completeMetricUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeMetricUpToEventFlow_injective heq)

theorem CompleteMetricUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier CompleteMetricUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate CompleteMetricUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨completeMetricUpBHistCarrier⟩, ⟨completeMetricUpChapterTasteGate⟩⟩

end BEDC.Derived.CompleteMetricUp
