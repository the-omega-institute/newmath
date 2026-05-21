import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyBoundedUp : Type where
  | mk (metricCarrier eps net coverage stability ledger nameCert : BHist) :
      TotallyBoundedUp

def TotallyBoundedUpTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def totallyBoundedUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedUpEncodeBHist h

def totallyBoundedUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedUpDecodeBHist tail)

private theorem totallyBoundedUp_decode_encode_bhist :
    ∀ h : BHist, totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def totallyBoundedUpToEventFlow : TotallyBoundedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedUp.mk metricCarrier eps net coverage stability ledger nameCert =>
      [TotallyBoundedUpTasteGate_single_carrier_alignment_tag,
        totallyBoundedUpEncodeBHist metricCarrier,
        totallyBoundedUpEncodeBHist eps,
        totallyBoundedUpEncodeBHist net,
        totallyBoundedUpEncodeBHist coverage,
        totallyBoundedUpEncodeBHist stability,
        totallyBoundedUpEncodeBHist ledger,
        totallyBoundedUpEncodeBHist nameCert]

def totallyBoundedUpFromEventFlow : EventFlow → Option TotallyBoundedUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | metricCarrier :: rest1 =>
          match rest1 with
          | [] => none
          | eps :: rest2 =>
              match rest2 with
              | [] => none
              | net :: rest3 =>
                  match rest3 with
                  | [] => none
                  | coverage :: rest4 =>
                      match rest4 with
                      | [] => none
                      | stability :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | nameCert :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (TotallyBoundedUp.mk
                                          (totallyBoundedUpDecodeBHist metricCarrier)
                                          (totallyBoundedUpDecodeBHist eps)
                                          (totallyBoundedUpDecodeBHist net)
                                          (totallyBoundedUpDecodeBHist coverage)
                                          (totallyBoundedUpDecodeBHist stability)
                                          (totallyBoundedUpDecodeBHist ledger)
                                          (totallyBoundedUpDecodeBHist nameCert))
                                  | _ :: _ => none

private theorem totallyBoundedUp_round_trip :
    ∀ x : TotallyBoundedUp,
      totallyBoundedUpFromEventFlow (totallyBoundedUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricCarrier eps net coverage stability ledger nameCert =>
      change
        some
          (TotallyBoundedUp.mk
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist metricCarrier))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist eps))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist net))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist coverage))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist stability))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist ledger))
            (totallyBoundedUpDecodeBHist (totallyBoundedUpEncodeBHist nameCert))) =
          some
            (TotallyBoundedUp.mk metricCarrier eps net coverage stability ledger nameCert)
      rw [totallyBoundedUp_decode_encode_bhist metricCarrier,
        totallyBoundedUp_decode_encode_bhist eps,
        totallyBoundedUp_decode_encode_bhist net,
        totallyBoundedUp_decode_encode_bhist coverage,
        totallyBoundedUp_decode_encode_bhist stability,
        totallyBoundedUp_decode_encode_bhist ledger,
        totallyBoundedUp_decode_encode_bhist nameCert]

private theorem totallyBoundedUpToEventFlow_injective {x y : TotallyBoundedUp} :
    totallyBoundedUpToEventFlow x = totallyBoundedUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedUpFromEventFlow (totallyBoundedUpToEventFlow x) =
        totallyBoundedUpFromEventFlow (totallyBoundedUpToEventFlow y) :=
    congrArg totallyBoundedUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totallyBoundedUp_round_trip x).symm
      (Eq.trans hread (totallyBoundedUp_round_trip y)))

instance totallyBoundedUpBHistCarrier : BHistCarrier TotallyBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedUpToEventFlow
  fromEventFlow := totallyBoundedUpFromEventFlow

instance totallyBoundedUpChapterTasteGate : ChapterTasteGate TotallyBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totallyBoundedUpFromEventFlow (totallyBoundedUpToEventFlow x) = some x
    exact totallyBoundedUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totallyBoundedUpToEventFlow_injective heq)

theorem TotallyBoundedUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier TotallyBoundedUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate TotallyBoundedUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨totallyBoundedUpBHistCarrier⟩, ⟨totallyBoundedUpChapterTasteGate⟩⟩

end BEDC.Derived.TotallyBoundedUp
