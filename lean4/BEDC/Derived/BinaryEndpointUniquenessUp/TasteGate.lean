import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinaryEndpointUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinaryEndpointUniquenessUp : Type where
  | mk : (binary normalization digit window handoff terminalSeal transport : BHist) →
      BinaryEndpointUniquenessUp
  deriving DecidableEq

def BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist h

def BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields :
    BinaryEndpointUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryEndpointUniquenessUp.mk binary normalization digit window handoff terminalSeal
      transport =>
      [binary, normalization, digit, window, handoff, terminalSeal, transport]

def BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow :
    BinaryEndpointUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b0, BMark.b1, BMark.b1, BMark.b0] ::
        (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields x).map
          BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist

def BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BinaryEndpointUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: binary :: normalization :: digit :: window :: handoff :: terminalSeal ::
      transport :: [] =>
      some
        (BinaryEndpointUniquenessUp.mk
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist binary)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist normalization)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist digit)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist window)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist handoff)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist terminalSeal)
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist transport))
  | _ => none

private theorem BinaryEndpointUniquenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BinaryEndpointUniquenessUp,
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk binary normalization digit window handoff terminalSeal transport =>
      change
        some
          (BinaryEndpointUniquenessUp.mk
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist binary))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist normalization))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist digit))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist window))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist handoff))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist terminalSeal))
            (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
              (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist transport))) =
          some
            (BinaryEndpointUniquenessUp.mk binary normalization digit window handoff terminalSeal
              transport)
      rw [BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode binary,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode normalization,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode digit,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode window,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode handoff,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode terminalSeal,
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode transport]

private theorem BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BinaryEndpointUniquenessUp} :
    BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow x =
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow x) =
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BinaryEndpointUniquenessUp,
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields x =
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk binary₁ normalization₁ digit₁ window₁ handoff₁ terminalSeal₁ transport₁ =>
      cases y with
      | mk binary₂ normalization₂ digit₂ window₂ handoff₂ terminalSeal₂ transport₂ =>
          injection hfields with hbinary tail1
          injection tail1 with hnormalization tail2
          injection tail2 with hdigit tail3
          injection tail3 with hwindow tail4
          injection tail4 with hhandoff tail5
          injection tail5 with hterminalSeal tail6
          injection tail6 with htransport _
          subst hbinary
          subst hnormalization
          subst hdigit
          subst hwindow
          subst hhandoff
          subst hterminalSeal
          subst htransport
          rfl

instance binaryEndpointUniquenessBHistCarrier :
    BHistCarrier BinaryEndpointUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow

instance binaryEndpointUniquenessChapterTasteGate :
    ChapterTasteGate BinaryEndpointUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fromEventFlow
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BinaryEndpointUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance binaryEndpointUniquenessFieldFaithful :
    FieldFaithful BinaryEndpointUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields
  field_faithful :=
    BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields_faithful

instance binaryEndpointUniquenessNontrivial :
    Nontrivial BinaryEndpointUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BinaryEndpointUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BinaryEndpointUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hbinary
        cases hbinary⟩

def taste_gate : ChapterTasteGate BinaryEndpointUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  binaryEndpointUniquenessChapterTasteGate

theorem BinaryEndpointUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decodeBHist
          (BinaryEndpointUniquenessTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      BinaryEndpointUniquenessTasteGate_single_carrier_alignment_fields
          (BinaryEndpointUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] ∧
        BinaryEndpointUniquenessTasteGate_single_carrier_alignment_toEventFlow
            (BinaryEndpointUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b0, BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BinaryEndpointUniquenessTasteGate_single_carrier_alignment_decode_encode, rfl, rfl⟩

end BEDC.Derived.BinaryEndpointUniquenessUp
