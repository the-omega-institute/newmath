import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionInductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionInductionUp : Type where
  | mk :
      (denseSource finiteWindow dyadicTolerance regularReadback realSeal extensionFace
        uniquenessLedger transport replay provenance localNameCert : BHist) →
      BishopCompletionInductionUp
  deriving DecidableEq

def bishopCompletionInductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionInductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionInductionEncodeBHist h

def bishopCompletionInductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionInductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionInductionDecodeBHist tail)

theorem BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopCompletionInductionFields : BishopCompletionInductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionInductionUp.mk denseSource finiteWindow dyadicTolerance regularReadback
      realSeal extensionFace uniquenessLedger transport replay provenance localNameCert =>
      [denseSource, finiteWindow, dyadicTolerance, regularReadback, realSeal, extensionFace,
        uniquenessLedger, transport, replay, provenance, localNameCert]

def bishopCompletionInductionToEventFlow : BishopCompletionInductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompletionInductionFields x).map bishopCompletionInductionEncodeBHist

def bishopCompletionInductionFromEventFlow : EventFlow → Option BishopCompletionInductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | denseSource :: rest0 =>
      match rest0 with
      | [] => none
      | finiteWindow :: rest1 =>
          match rest1 with
          | [] => none
          | dyadicTolerance :: rest2 =>
              match rest2 with
              | [] => none
              | regularReadback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | extensionFace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | uniquenessLedger :: rest6 =>
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
                                          | localNameCert :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BishopCompletionInductionUp.mk
                                                      (bishopCompletionInductionDecodeBHist
                                                        denseSource)
                                                      (bishopCompletionInductionDecodeBHist
                                                        finiteWindow)
                                                      (bishopCompletionInductionDecodeBHist
                                                        dyadicTolerance)
                                                      (bishopCompletionInductionDecodeBHist
                                                        regularReadback)
                                                      (bishopCompletionInductionDecodeBHist
                                                        realSeal)
                                                      (bishopCompletionInductionDecodeBHist
                                                        extensionFace)
                                                      (bishopCompletionInductionDecodeBHist
                                                        uniquenessLedger)
                                                      (bishopCompletionInductionDecodeBHist
                                                        transport)
                                                      (bishopCompletionInductionDecodeBHist
                                                        replay)
                                                      (bishopCompletionInductionDecodeBHist
                                                        provenance)
                                                      (bishopCompletionInductionDecodeBHist
                                                        localNameCert))
                                              | _ :: _ => none

theorem BishopCompletionInductionUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompletionInductionUp,
      bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk denseSource finiteWindow dyadicTolerance regularReadback realSeal extensionFace
      uniquenessLedger transport replay provenance localNameCert =>
      change
        some
          (BishopCompletionInductionUp.mk
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist denseSource))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist finiteWindow))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist dyadicTolerance))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist regularReadback))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist realSeal))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist extensionFace))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist uniquenessLedger))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist transport))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist replay))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist provenance))
            (bishopCompletionInductionDecodeBHist
              (bishopCompletionInductionEncodeBHist localNameCert))) =
          some
            (BishopCompletionInductionUp.mk denseSource finiteWindow dyadicTolerance
              regularReadback realSeal extensionFace uniquenessLedger transport replay provenance
              localNameCert)
      rw [BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode
        denseSource,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode finiteWindow,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode
          dyadicTolerance,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode
          regularReadback,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode realSeal,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode extensionFace,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode
          uniquenessLedger,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode transport,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode replay,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode provenance,
        BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode localNameCert]

theorem BishopCompletionInductionUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionInductionUp} :
    bishopCompletionInductionToEventFlow x = bishopCompletionInductionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow x) =
        bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow y) :=
    congrArg bishopCompletionInductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompletionInductionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionInductionUpTasteGate_single_carrier_alignment_round_trip y)))

theorem BishopCompletionInductionUpTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BishopCompletionInductionUp,
      bishopCompletionInductionFields x = bishopCompletionInductionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk denseSource₁ finiteWindow₁ dyadicTolerance₁ regularReadback₁ realSeal₁
      extensionFace₁ uniquenessLedger₁ transport₁ replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk denseSource₂ finiteWindow₂ dyadicTolerance₂ regularReadback₂ realSeal₂
          extensionFace₂ uniquenessLedger₂ transport₂ replay₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance bishopCompletionInductionBHistCarrier :
    BHistCarrier BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionInductionToEventFlow
  fromEventFlow := bishopCompletionInductionFromEventFlow

instance bishopCompletionInductionChapterTasteGate :
    ChapterTasteGate BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (BishopCompletionInductionUpTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompletionInductionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopCompletionInductionFieldFaithful :
    FieldFaithful BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompletionInductionFields
  field_faithful := BishopCompletionInductionUpTasteGate_single_carrier_alignment_field_faithful

instance bishopCompletionInductionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompletionInductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCompletionInductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def BishopCompletionInductionUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BishopCompletionInductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompletionInductionChapterTasteGate

theorem BishopCompletionInductionUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopCompletionInductionUp) ∧
      Nonempty (FieldFaithful BishopCompletionInductionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopCompletionInductionUp) ∧
          (∀ h : BHist,
            bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist h) =
              h) ∧
            (∀ x : BishopCompletionInductionUp,
              bishopCompletionInductionFromEventFlow
                  (bishopCompletionInductionToEventFlow x) =
                some x) ∧
              (∀ x y : BishopCompletionInductionUp,
                bishopCompletionInductionToEventFlow x =
                    bishopCompletionInductionToEventFlow y →
                  x = y) ∧
                bishopCompletionInductionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨bishopCompletionInductionChapterTasteGate⟩
  · constructor
    · exact ⟨bishopCompletionInductionFieldFaithful⟩
    · constructor
      · exact ⟨bishopCompletionInductionNontrivial⟩
      · constructor
        · exact BishopCompletionInductionUpTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact BishopCompletionInductionUpTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                BishopCompletionInductionUpTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.BishopCompletionInductionUp
