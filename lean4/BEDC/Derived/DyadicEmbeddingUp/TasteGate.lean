import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicEmbeddingUp : Type where
  | mk :
      (dyadic stream readback realSeal transport route provenance nameCert : BHist) →
      DyadicEmbeddingUp
  deriving DecidableEq

def DyadicEmbeddingTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist h

def DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DyadicEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
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

def DyadicEmbeddingTasteGate_single_carrier_alignment_fields :
    DyadicEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicEmbeddingUp.mk dyadic stream readback realSeal transport route provenance
      nameCert =>
      [dyadic, stream, readback, realSeal, transport, route, provenance, nameCert]

def DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow :
    DyadicEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      DyadicEmbeddingTasteGate_single_carrier_alignment_tag ::
        (DyadicEmbeddingTasteGate_single_carrier_alignment_fields x).map
          DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist

def DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DyadicEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, dyadic, stream, readback, realSeal, transport, route, provenance, nameCert] =>
      match tag with
      | [BMark.b1, BMark.b1, BMark.b0] =>
          some
            (DyadicEmbeddingUp.mk
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist dyadic)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist stream)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist readback)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist realSeal)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist transport)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist route)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist provenance)
              (DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist nameCert))
      | _ => none
  | _ => none

private theorem DyadicEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicEmbeddingUp,
      DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadic stream readback realSeal transport route provenance nameCert =>
      simp only [DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow,
        DyadicEmbeddingTasteGate_single_carrier_alignment_fields,
        DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DyadicEmbeddingTasteGate_single_carrier_alignment_tag,
        DyadicEmbeddingTasteGate_single_carrier_alignment_decode_encode]

private theorem DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicEmbeddingUp} :
    DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow x =
        DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicEmbeddingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DyadicEmbeddingUp,
      DyadicEmbeddingTasteGate_single_carrier_alignment_fields x =
          DyadicEmbeddingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk dyadic₁ stream₁ readback₁ realSeal₁ transport₁ route₁ provenance₁ nameCert₁ =>
      cases y with
      | mk dyadic₂ stream₂ readback₂ realSeal₂ transport₂ route₂ provenance₂ nameCert₂ =>
          injection hfields with hDyadic tail0
          injection tail0 with hStream tail1
          injection tail1 with hReadback tail2
          injection tail2 with hRealSeal tail3
          injection tail3 with hTransport tail4
          injection tail4 with hRoute tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hNameCert _
          subst hDyadic
          subst hStream
          subst hReadback
          subst hRealSeal
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hNameCert
          rfl

instance DyadicEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow

instance DyadicEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DyadicEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DyadicEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance DyadicEmbeddingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful DyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DyadicEmbeddingTasteGate_single_carrier_alignment_fields
  field_faithful := DyadicEmbeddingTasteGate_single_carrier_alignment_field_faithful

instance DyadicEmbeddingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial DyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DyadicEmbeddingTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate

theorem DyadicEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        DyadicEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (DyadicEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      DyadicEmbeddingTasteGate_single_carrier_alignment_toEventFlow
          (DyadicEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact DyadicEmbeddingTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.DyadicEmbeddingUp
