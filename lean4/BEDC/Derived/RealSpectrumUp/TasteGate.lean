import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSpectrumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSpectrumUp : Type where
  | mk
      (banachAlgebra algebraElement boundedOperator realSeal regseqReadback spectralWindow
        resolventBoundary spectralRadiusEstimate spectrumReadback transport replay provenance
        localNameCert : BHist) :
        RealSpectrumUp
  deriving DecidableEq

def RealSpectrumTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1]

def RealSpectrumTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RealSpectrumTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RealSpectrumTasteGate_single_carrier_alignment_encodeBHist h

def RealSpectrumTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealSpectrumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
          (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RealSpectrumTasteGate_single_carrier_alignment_fields :
    RealSpectrumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSpectrumUp.mk banachAlgebra algebraElement boundedOperator realSeal regseqReadback
      spectralWindow resolventBoundary spectralRadiusEstimate spectrumReadback transport replay
      provenance localNameCert =>
      [banachAlgebra, algebraElement, boundedOperator, realSeal, regseqReadback, spectralWindow,
        resolventBoundary, spectralRadiusEstimate, spectrumReadback, transport, replay,
        provenance, localNameCert]

def RealSpectrumTasteGate_single_carrier_alignment_toEventFlow :
    RealSpectrumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSpectrumUp.mk banachAlgebra algebraElement boundedOperator realSeal regseqReadback
      spectralWindow resolventBoundary spectralRadiusEstimate spectrumReadback transport replay
      provenance localNameCert =>
      [RealSpectrumTasteGate_single_carrier_alignment_tag,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist banachAlgebra,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist algebraElement,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist boundedOperator,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist realSeal,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist regseqReadback,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist spectralWindow,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist resolventBoundary,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist spectralRadiusEstimate,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist spectrumReadback,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist transport,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist replay,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist provenance,
        RealSpectrumTasteGate_single_carrier_alignment_encodeBHist localNameCert]

private def RealSpectrumTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealSpectrumTasteGate_single_carrier_alignment_eventAt index rest

def RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RealSpectrumUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealSpectrumUp.mk
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 1 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 2 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 3 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 4 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 5 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 6 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 7 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 8 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 9 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 10 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 11 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 12 ef))
          (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
            (RealSpectrumTasteGate_single_carrier_alignment_eventAt 13 ef)))

private theorem RealSpectrumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealSpectrumUp,
      RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow
          (RealSpectrumTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk banachAlgebra algebraElement boundedOperator realSeal regseqReadback spectralWindow
      resolventBoundary spectralRadiusEstimate spectrumReadback transport replay provenance
      localNameCert =>
      change
        some
          (RealSpectrumUp.mk
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist banachAlgebra))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist algebraElement))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist boundedOperator))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist realSeal))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist regseqReadback))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist spectralWindow))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist resolventBoundary))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist
                spectralRadiusEstimate))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist spectrumReadback))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist transport))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist replay))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist provenance))
            (RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
              (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (RealSpectrumUp.mk banachAlgebra algebraElement boundedOperator realSeal
              regseqReadback spectralWindow resolventBoundary spectralRadiusEstimate
              spectrumReadback transport replay provenance localNameCert)
      rw [RealSpectrumTasteGate_single_carrier_alignment_decode_encode banachAlgebra,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode algebraElement,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode boundedOperator,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode realSeal,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode regseqReadback,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode spectralWindow,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode resolventBoundary,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode spectralRadiusEstimate,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode spectrumReadback,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode transport,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode replay,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode provenance,
        RealSpectrumTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem RealSpectrumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSpectrumUp} :
    RealSpectrumTasteGate_single_carrier_alignment_toEventFlow x =
        RealSpectrumTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow
          (RealSpectrumTasteGate_single_carrier_alignment_toEventFlow x) =
        RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow
          (RealSpectrumTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealSpectrumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSpectrumTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealSpectrumTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealSpectrumUp,
      RealSpectrumTasteGate_single_carrier_alignment_fields x =
          RealSpectrumTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk banachAlgebra₁ algebraElement₁ boundedOperator₁ realSeal₁ regseqReadback₁
      spectralWindow₁ resolventBoundary₁ spectralRadiusEstimate₁ spectrumReadback₁
      transport₁ replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk banachAlgebra₂ algebraElement₂ boundedOperator₂ realSeal₂ regseqReadback₂
          spectralWindow₂ resolventBoundary₂ spectralRadiusEstimate₂ spectrumReadback₂
          transport₂ replay₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance RealSpectrumTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RealSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealSpectrumTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow

instance RealSpectrumTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RealSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealSpectrumTasteGate_single_carrier_alignment_fromEventFlow
          (RealSpectrumTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RealSpectrumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSpectrumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RealSpectrumTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RealSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RealSpectrumTasteGate_single_carrier_alignment_fields
  field_faithful := RealSpectrumTasteGate_single_carrier_alignment_fields_faithful

instance RealSpectrumTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RealSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSpectrumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealSpectrumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealSpectrumTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealSpectrumTasteGate_single_carrier_alignment_ChapterTasteGate

theorem RealSpectrumTasteGate_single_carrier_alignment :
    (forall h : BHist,
      RealSpectrumTasteGate_single_carrier_alignment_decodeBHist
          (RealSpectrumTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      RealSpectrumTasteGate_single_carrier_alignment_fields
          (RealSpectrumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealSpectrumTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.RealSpectrumUp
