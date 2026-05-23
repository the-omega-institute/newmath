import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalCompactUp : Type where
  | mk
      (lowerEndpoint upperEndpoint finiteWindow toleranceScale finiteGrid rationalWitness
        comparisonRow transport replay provenance localNameCert : BHist) :
        BishopIntervalCompactUp
  deriving DecidableEq

def BishopIntervalCompactTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist h

def BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
          (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopIntervalCompactTasteGate_single_carrier_alignment_fields :
    BishopIntervalCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalCompactUp.mk lowerEndpoint upperEndpoint finiteWindow toleranceScale finiteGrid
      rationalWitness comparisonRow transport replay provenance localNameCert =>
      [lowerEndpoint, upperEndpoint, finiteWindow, toleranceScale, finiteGrid, rationalWitness,
        comparisonRow, transport, replay, provenance, localNameCert]

def BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow :
    BishopIntervalCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalCompactUp.mk lowerEndpoint upperEndpoint finiteWindow toleranceScale finiteGrid
      rationalWitness comparisonRow transport replay provenance localNameCert =>
      [BishopIntervalCompactTasteGate_single_carrier_alignment_tag,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist lowerEndpoint,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist upperEndpoint,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist finiteWindow,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist toleranceScale,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist finiteGrid,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist rationalWitness,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist comparisonRow,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist transport,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist replay,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist provenance,
        BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist localNameCert]

private def BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt index rest

def BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BishopIntervalCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopIntervalCompactUp.mk
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 1 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 2 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 3 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 4 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 5 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 6 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 7 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 8 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 9 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 10 ef))
          (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
            (BishopIntervalCompactTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem BishopIntervalCompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopIntervalCompactUp,
      BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow
          (BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lowerEndpoint upperEndpoint finiteWindow toleranceScale finiteGrid rationalWitness
      comparisonRow transport replay provenance localNameCert =>
      change
        some
          (BishopIntervalCompactUp.mk
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist lowerEndpoint))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist upperEndpoint))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist finiteWindow))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist toleranceScale))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist finiteGrid))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist rationalWitness))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist comparisonRow))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist transport))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist replay))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist provenance))
            (BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
              (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (BishopIntervalCompactUp.mk lowerEndpoint upperEndpoint finiteWindow toleranceScale
              finiteGrid rationalWitness comparisonRow transport replay provenance localNameCert)
      rw [BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode lowerEndpoint,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode upperEndpoint,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode finiteWindow,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode toleranceScale,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode finiteGrid,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode rationalWitness,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode comparisonRow,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode transport,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode replay,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode provenance,
        BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopIntervalCompactUp} :
    BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow x =
        BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow
          (BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow x) =
        BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow
          (BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopIntervalCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopIntervalCompactTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopIntervalCompactTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopIntervalCompactUp,
      BishopIntervalCompactTasteGate_single_carrier_alignment_fields x =
          BishopIntervalCompactTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lowerEndpoint₁ upperEndpoint₁ finiteWindow₁ toleranceScale₁ finiteGrid₁ rationalWitness₁
      comparisonRow₁ transport₁ replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk lowerEndpoint₂ upperEndpoint₂ finiteWindow₂ toleranceScale₂ finiteGrid₂
          rationalWitness₂ comparisonRow₂ transport₂ replay₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance BishopIntervalCompactTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BishopIntervalCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow

instance BishopIntervalCompactTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BishopIntervalCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopIntervalCompactTasteGate_single_carrier_alignment_fromEventFlow
          (BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BishopIntervalCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BishopIntervalCompactTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BishopIntervalCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BishopIntervalCompactTasteGate_single_carrier_alignment_fields
  field_faithful := BishopIntervalCompactTasteGate_single_carrier_alignment_fields_faithful

theorem BishopIntervalCompactTasteGate_single_carrier_alignment :
    (forall h : BHist,
      BishopIntervalCompactTasteGate_single_carrier_alignment_decodeBHist
          (BishopIntervalCompactTasteGate_single_carrier_alignment_encodeBHist h) =
        h) /\
      BishopIntervalCompactTasteGate_single_carrier_alignment_fields
          (BishopIntervalCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] /\
        BishopIntervalCompactTasteGate_single_carrier_alignment_toEventFlow
            (BishopIntervalCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [[BMark.b1, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopIntervalCompactTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.BishopIntervalCompactUp
