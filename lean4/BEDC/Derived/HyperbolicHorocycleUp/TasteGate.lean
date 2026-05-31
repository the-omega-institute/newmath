import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicHorocycleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicHorocycleUp : Type where
  | mk :
      (disk metric boundary geodesic transport ledger hsameRow replay provenance name : BHist) →
        HyperbolicHorocycleUp

def HyperbolicHorocycleTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b0]

def HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist h

def HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
          (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist h) =
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

def HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow :
    HyperbolicHorocycleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicHorocycleUp.mk disk metric boundary geodesic transport ledger hsameRow replay
      provenance name =>
      [HyperbolicHorocycleTasteGate_single_carrier_alignment_tag,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist disk,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist metric,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist boundary,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist geodesic,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist transport,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist ledger,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist hsameRow,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist replay,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist provenance,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist name]

def HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option HyperbolicHorocycleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | disk :: rest1 =>
          match rest1 with
          | [] => none
          | metric :: rest2 =>
              match rest2 with
              | [] => none
              | boundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | geodesic :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | hsameRow :: rest7 =>
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
                                                    (HyperbolicHorocycleUp.mk
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        disk)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        metric)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        boundary)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        geodesic)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        transport)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        ledger)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        hsameRow)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        replay)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        provenance)
                                                      (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
                                                        name))
                                              | _ :: _ => none

private theorem HyperbolicHorocycleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyperbolicHorocycleUp,
      HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk disk metric boundary geodesic transport ledger hsameRow replay provenance name =>
      change
        some
          (HyperbolicHorocycleUp.mk
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist disk))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist metric))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist boundary))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist geodesic))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist transport))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist ledger))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist hsameRow))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist replay))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist provenance))
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist name))) =
          some
            (HyperbolicHorocycleUp.mk disk metric boundary geodesic transport ledger hsameRow
              replay provenance name)
      rw [HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode disk,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode metric,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode boundary,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode geodesic,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode transport,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode ledger,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode hsameRow,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode replay,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode provenance,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode name]

private theorem HyperbolicHorocycleTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicHorocycleUp} :
    HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x =
        HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x) =
        HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperbolicHorocycleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HyperbolicHorocycleTasteGate_single_carrier_alignment_round_trip y)))

instance HyperbolicHorocycleTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier HyperbolicHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow

instance HyperbolicHorocycleTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact HyperbolicHorocycleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicHorocycleTasteGate_single_carrier_alignment_injective heq)

theorem HyperbolicHorocycleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_decodeBHist
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      (∀ x : HyperbolicHorocycleUp,
        HyperbolicHorocycleTasteGate_single_carrier_alignment_fromEventFlow
            (HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
        (∀ x y : HyperbolicHorocycleUp,
          HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow x =
              HyperbolicHorocycleTasteGate_single_carrier_alignment_toEventFlow y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HyperbolicHorocycleTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HyperbolicHorocycleTasteGate_single_carrier_alignment_round_trip
    · intro x y heq
      exact HyperbolicHorocycleTasteGate_single_carrier_alignment_injective heq

end BEDC.Derived.HyperbolicHorocycleUp
