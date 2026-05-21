import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuedFractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuedFractionUp : Type where
  | mk :
      (partialQuotients numerator denominator errorRadius schedule handoff boundary ledger
        provenance : BHist) →
        ContinuedFractionUp
  deriving DecidableEq

def ContinuedFractionTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b1]

def ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist h

def ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ContinuedFractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
          (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist h) =
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

def ContinuedFractionTasteGate_single_carrier_alignment_fields :
    ContinuedFractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuedFractionUp.mk partialQuotients numerator denominator errorRadius schedule handoff
      boundary ledger provenance =>
      [partialQuotients, numerator, denominator, errorRadius, schedule, handoff, boundary,
        ledger, provenance]

def ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow :
    ContinuedFractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuedFractionUp.mk partialQuotients numerator denominator errorRadius schedule handoff
      boundary ledger provenance =>
      [ContinuedFractionTasteGate_single_carrier_alignment_tag,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist partialQuotients,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist numerator,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist denominator,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist errorRadius,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist schedule,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist handoff,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist boundary,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist ledger,
        ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist provenance]

def ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ContinuedFractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag :: rest0 =>
      match tag with
      | [BMark.b1, BMark.b1, BMark.b0, BMark.b1] =>
          match rest0 with
          | [] => none
          | partialQuotients :: rest1 =>
              match rest1 with
              | [] => none
              | numerator :: rest2 =>
                  match rest2 with
                  | [] => none
                  | denominator :: rest3 =>
                      match rest3 with
                      | [] => none
                      | errorRadius :: rest4 =>
                          match rest4 with
                          | [] => none
                          | schedule :: rest5 =>
                              match rest5 with
                              | [] => none
                              | handoff :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | boundary :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | ledger :: rest8 =>
                                          match rest8 with
                                          | [] => none
                                          | provenance :: rest9 =>
                                              match rest9 with
                                              | [] =>
                                                  some
                                                    (ContinuedFractionUp.mk
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        partialQuotients)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        numerator)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        denominator)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        errorRadius)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        schedule)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        handoff)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        boundary)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        ledger)
                                                      (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
                                                        provenance))
                                              | _ :: _ => none
      | _ => none

private theorem ContinuedFractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContinuedFractionUp,
      ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk partialQuotients numerator denominator errorRadius schedule handoff boundary ledger
      provenance =>
      change
        some
          (ContinuedFractionUp.mk
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist
                partialQuotients))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist numerator))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist denominator))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist errorRadius))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist schedule))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist handoff))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist boundary))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist ledger))
            (ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist provenance))) =
          some
            (ContinuedFractionUp.mk partialQuotients numerator denominator errorRadius schedule
              handoff boundary ledger provenance)
      rw [ContinuedFractionTasteGate_single_carrier_alignment_decode_encode partialQuotients,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode numerator,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode denominator,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode errorRadius,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode schedule,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode handoff,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode boundary,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode ledger,
        ContinuedFractionTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuedFractionUp} :
    ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow x =
        ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow x) =
        ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContinuedFractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContinuedFractionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContinuedFractionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ContinuedFractionUp,
      ContinuedFractionTasteGate_single_carrier_alignment_fields x =
          ContinuedFractionTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk partialQuotients₁ numerator₁ denominator₁ errorRadius₁ schedule₁ handoff₁ boundary₁
      ledger₁ provenance₁ =>
      cases y with
      | mk partialQuotients₂ numerator₂ denominator₂ errorRadius₂ schedule₂ handoff₂
          boundary₂ ledger₂ provenance₂ =>
          injection hfields with hPartialQuotients tail0
          injection tail0 with hNumerator tail1
          injection tail1 with hDenominator tail2
          injection tail2 with hErrorRadius tail3
          injection tail3 with hSchedule tail4
          injection tail4 with hHandoff tail5
          injection tail5 with hBoundary tail6
          injection tail6 with hLedger tail7
          injection tail7 with hProvenance _
          subst hPartialQuotients
          subst hNumerator
          subst hDenominator
          subst hErrorRadius
          subst hSchedule
          subst hHandoff
          subst hBoundary
          subst hLedger
          subst hProvenance
          rfl

instance ContinuedFractionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow

instance ContinuedFractionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ContinuedFractionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ContinuedFractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContinuedFractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ContinuedFractionTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful ContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ContinuedFractionTasteGate_single_carrier_alignment_fields
  field_faithful := ContinuedFractionTasteGate_single_carrier_alignment_fields_faithful

instance ContinuedFractionTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial ContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuedFractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuedFractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ContinuedFractionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ContinuedFractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ContinuedFractionTasteGate_single_carrier_alignment_ChapterTasteGate

theorem ContinuedFractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      ContinuedFractionTasteGate_single_carrier_alignment_decodeBHist
          (ContinuedFractionTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      ContinuedFractionTasteGate_single_carrier_alignment_fields
          (ContinuedFractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ContinuedFractionTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.ContinuedFractionUp
