import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NullSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NullSequenceUp : Type where
  | mk :
      (difference tolerance window modulus sealField transportField classifier provenance localNameCert :
        BHist) →
        NullSequenceUp
  deriving DecidableEq

def NullSequenceTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b0]

def NullSequenceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: NullSequenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: NullSequenceTasteGate_single_carrier_alignment_encodeBHist h

def NullSequenceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (NullSequenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (NullSequenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NullSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      NullSequenceTasteGate_single_carrier_alignment_decodeBHist
          (NullSequenceTasteGate_single_carrier_alignment_encodeBHist h) =
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

def NullSequenceTasteGate_single_carrier_alignment_fields :
    NullSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NullSequenceUp.mk difference tolerance window modulus sealField transportField classifier provenance
      localNameCert =>
      [difference, tolerance, window, modulus, sealField, transportField, classifier, provenance,
        localNameCert]

def NullSequenceTasteGate_single_carrier_alignment_toEventFlow :
    NullSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NullSequenceUp.mk difference tolerance window modulus sealField transportField classifier provenance
      localNameCert =>
      [NullSequenceTasteGate_single_carrier_alignment_tag,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist difference,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist tolerance,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist window,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist modulus,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist sealField,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist transportField,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist classifier,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist provenance,
        NullSequenceTasteGate_single_carrier_alignment_encodeBHist localNameCert]

def NullSequenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option NullSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag :: rest0 =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b1, BMark.b0] =>
          match rest0 with
          | [] => none
          | difference :: rest1 =>
              match rest1 with
              | [] => none
              | tolerance :: rest2 =>
                  match rest2 with
                  | [] => none
                  | window :: rest3 =>
                      match rest3 with
                      | [] => none
                      | modulus :: rest4 =>
                          match rest4 with
                          | [] => none
                          | sealField :: rest5 =>
                              match rest5 with
                              | [] => none
                              | transportField :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | classifier :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | provenance :: rest8 =>
                                          match rest8 with
                                          | [] => none
                                          | localNameCert :: rest9 =>
                                              match rest9 with
                                              | [] =>
                                                  some
                                                    (NullSequenceUp.mk
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        difference)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        tolerance)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        window)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        modulus)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        sealField)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        transportField)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        classifier)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        provenance)
                                                      (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
                                                        localNameCert))
                                              | _ :: _ => none
      | _ => none

private theorem NullSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NullSequenceUp,
      NullSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (NullSequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk difference tolerance window modulus sealField transportField classifier provenance localNameCert =>
      change
        some
          (NullSequenceUp.mk
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist difference))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist tolerance))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist window))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist modulus))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist sealField))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist transportField))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist classifier))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist provenance))
            (NullSequenceTasteGate_single_carrier_alignment_decodeBHist
              (NullSequenceTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (NullSequenceUp.mk difference tolerance window modulus sealField transportField classifier
              provenance localNameCert)
      rw [NullSequenceTasteGate_single_carrier_alignment_decode_encode difference,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode tolerance,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode window,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode modulus,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode sealField,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode transportField,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode classifier,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode provenance,
        NullSequenceTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem NullSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NullSequenceUp} :
    NullSequenceTasteGate_single_carrier_alignment_toEventFlow x =
        NullSequenceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      NullSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (NullSequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        NullSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (NullSequenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg NullSequenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NullSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NullSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem NullSequenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NullSequenceUp,
      NullSequenceTasteGate_single_carrier_alignment_fields x =
          NullSequenceTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk difference₁ tolerance₁ window₁ modulus₁ seal₁ transport₁ classifier₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk difference₂ tolerance₂ window₂ modulus₂ seal₂ transport₂ classifier₂ provenance₂
          localNameCert₂ =>
          injection hfields with hDifference tail0
          injection tail0 with hTolerance tail1
          injection tail1 with hWindow tail2
          injection tail2 with hModulus tail3
          injection tail3 with hSeal tail4
          injection tail4 with hTransport tail5
          injection tail5 with hClassifier tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalNameCert _
          subst hDifference
          subst hTolerance
          subst hWindow
          subst hModulus
          subst hSeal
          subst hTransport
          subst hClassifier
          subst hProvenance
          subst hLocalNameCert
          rfl

instance NullSequenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier NullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NullSequenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NullSequenceTasteGate_single_carrier_alignment_fromEventFlow

instance NullSequenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate NullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      NullSequenceTasteGate_single_carrier_alignment_fromEventFlow
          (NullSequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact NullSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NullSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance NullSequenceTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful NullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := NullSequenceTasteGate_single_carrier_alignment_fields
  field_faithful := NullSequenceTasteGate_single_carrier_alignment_fields_faithful

instance NullSequenceTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial NullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NullSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NullSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def NullSequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate NullSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  NullSequenceTasteGate_single_carrier_alignment_ChapterTasteGate

theorem NullSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      NullSequenceTasteGate_single_carrier_alignment_decodeBHist
          (NullSequenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      NullSequenceTasteGate_single_carrier_alignment_fields
          (NullSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact NullSequenceTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.NullSequenceUp
