import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCompletenessUp : Type where
  | mk
      (B N C W R E H T P Q : BHist) :
      NestedIntervalCompletenessUp
  deriving DecidableEq

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields :
    NestedIntervalCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCompletenessUp.mk B N C W R E H T P Q => [B, N, C, W, R, E, H, T, P, Q]

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow :
    NestedIntervalCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields x).map
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option NestedIntervalCompletenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [B, N, C, W, R, E, H, T, P, Q] =>
      some
        (NestedIntervalCompletenessUp.mk
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist B)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist N)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist C)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist W)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist R)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist E)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist H)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist T)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist P)
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist Q))
  | _ => none

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedIntervalCompletenessUp,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B N C W R E H T P Q =>
      change
        some
          (NestedIntervalCompletenessUp.mk
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist B))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist N))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist C))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist W))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist R))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist E))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist H))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist T))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist P))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist Q))) =
          some (NestedIntervalCompletenessUp.mk B N C W R E H T P Q)
      rw [NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode B,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode N,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode C,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode W,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode R,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode E,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode H,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode T,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode P,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode Q]

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedIntervalCompletenessUp} :
    NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x =
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NestedIntervalCompletenessUp,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields x =
          NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ N₁ C₁ W₁ R₁ E₁ H₁ T₁ P₁ Q₁ =>
      cases y with
      | mk B₂ N₂ C₂ W₂ R₂ E₂ H₂ T₂ P₂ Q₂ =>
          cases hfields
          rfl

instance NestedIntervalCompletenessTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow

instance NestedIntervalCompletenessTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance NestedIntervalCompletenessTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields
  field_faithful :=
    NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields_faithful

instance NestedIntervalCompletenessTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedIntervalCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields
          (NestedIntervalCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.NestedIntervalCompletenessUp
