import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpenFitPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpenFitPacketUp : Type where
  | mk :
      (history packet signature model fit failure ledger boundary name : BHist) →
      OpenFitPacketUp
  deriving DecidableEq

def OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist h

def OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem OpenFitPacketTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
          (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist h) =
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

def OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow :
    OpenFitPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitPacketUp.mk history packet signature model fit failure ledger boundary name =>
      [[BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist history,
        [BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist packet,
        [BMark.b1, BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist model,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist fit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist name]

def OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option OpenFitPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | packet :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | signature :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | model :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | fit :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | failure :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | boundary :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (OpenFitPacketUp.mk
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    history)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    packet)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    signature)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    model)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    fit)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    failure)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    ledger)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    boundary)
                                                                                  (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem OpenFitPacketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OpenFitPacketUp,
      OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow
          (OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history packet signature model fit failure ledger boundary name =>
      change
        some
            (OpenFitPacketUp.mk
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist history))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist packet))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist signature))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist model))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist fit))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist failure))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist ledger))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist boundary))
              (OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
                (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist name))) =
          some
            (OpenFitPacketUp.mk history packet signature model fit failure ledger boundary
              name)
      rw [OpenFitPacketTasteGate_single_carrier_alignment_decode history,
        OpenFitPacketTasteGate_single_carrier_alignment_decode packet,
        OpenFitPacketTasteGate_single_carrier_alignment_decode signature,
        OpenFitPacketTasteGate_single_carrier_alignment_decode model,
        OpenFitPacketTasteGate_single_carrier_alignment_decode fit,
        OpenFitPacketTasteGate_single_carrier_alignment_decode failure,
        OpenFitPacketTasteGate_single_carrier_alignment_decode ledger,
        OpenFitPacketTasteGate_single_carrier_alignment_decode boundary,
        OpenFitPacketTasteGate_single_carrier_alignment_decode name]

private theorem OpenFitPacketTasteGate_single_carrier_alignment_injective
    {x y : OpenFitPacketUp} :
    OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow x =
        OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow
          (OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow x) =
        OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow
          (OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OpenFitPacketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OpenFitPacketTasteGate_single_carrier_alignment_round_trip y)))

private def OpenFitPacketTasteGate_single_carrier_alignment_fields :
    OpenFitPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitPacketUp.mk history packet signature model fit failure ledger boundary name =>
      [history, packet, signature, model, fit, failure, ledger, boundary, name]

private theorem OpenFitPacketTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : OpenFitPacketUp,
      OpenFitPacketTasteGate_single_carrier_alignment_fields x =
        OpenFitPacketTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk history packet signature model fit failure ledger boundary name =>
      cases y with
      | mk history' packet' signature' model' fit' failure' ledger' boundary' name' =>
          cases hfields
          rfl

instance openFitPacketBHistCarrier : BHistCarrier OpenFitPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow

instance openFitPacketChapterTasteGate : ChapterTasteGate OpenFitPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      OpenFitPacketTasteGate_single_carrier_alignment_fromEventFlow
          (OpenFitPacketTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact OpenFitPacketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OpenFitPacketTasteGate_single_carrier_alignment_injective heq)

instance openFitPacketFieldFaithful : FieldFaithful OpenFitPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := OpenFitPacketTasteGate_single_carrier_alignment_fields
  field_faithful := OpenFitPacketTasteGate_single_carrier_alignment_field_faithful

instance openFitPacketNontrivial : Nontrivial OpenFitPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OpenFitPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OpenFitPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OpenFitPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  openFitPacketChapterTasteGate

theorem OpenFitPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      OpenFitPacketTasteGate_single_carrier_alignment_decodeBHist
          (OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      (∀ x y : OpenFitPacketUp,
        OpenFitPacketTasteGate_single_carrier_alignment_fields x =
          OpenFitPacketTasteGate_single_carrier_alignment_fields y →
        x = y) ∧
        Nonempty (FieldFaithful OpenFitPacketUp) ∧
          Nonempty (Nontrivial OpenFitPacketUp) ∧
            OpenFitPacketTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
              ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact OpenFitPacketTasteGate_single_carrier_alignment_decode
  · constructor
    · exact OpenFitPacketTasteGate_single_carrier_alignment_field_faithful
    · constructor
      · exact ⟨openFitPacketFieldFaithful⟩
      · constructor
        · exact ⟨openFitPacketNontrivial⟩
        · rfl

end BEDC.Derived.OpenFitPacketUp
