import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalEmbeddingUp : Type where
  | mk (q S R D E H C : BHist) : RationalEmbeddingUp
  deriving DecidableEq

def RationalEmbeddingTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b0]

def RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist h

def RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RationalEmbeddingTasteGate_single_carrier_alignment_fields :
    RationalEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalEmbeddingUp.mk q S R D E H C => [q, S, R, D, E, H, C]

def RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow :
    RationalEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RationalEmbeddingUp.mk q S R D E H C =>
      [RationalEmbeddingTasteGate_single_carrier_alignment_tag,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist q,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist S,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist R,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist D,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist E,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist H,
        RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist C]

private def RationalEmbeddingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RationalEmbeddingTasteGate_single_carrier_alignment_eventAt index rest

def RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RationalEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RationalEmbeddingUp.mk
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 1 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 2 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 3 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 4 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 5 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 6 ef))
          (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
            (RationalEmbeddingTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem RationalEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalEmbeddingUp,
      RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q S R D E H C =>
      change
        some
          (RationalEmbeddingUp.mk
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist q))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist S))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist R))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist D))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist E))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist H))
            (RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
              (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist C))) =
          some (RationalEmbeddingUp.mk q S R D E H C)
      rw [RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode q,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode S,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode R,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode D,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode E,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode H,
        RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode C]

private theorem RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalEmbeddingUp} :
    RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow x =
        RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RationalEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalEmbeddingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RationalEmbeddingUp,
      RationalEmbeddingTasteGate_single_carrier_alignment_fields x =
          RationalEmbeddingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ S₁ R₁ D₁ E₁ H₁ C₁ =>
      cases y with
      | mk q₂ S₂ R₂ D₂ E₂ H₂ C₂ =>
          cases hfields
          rfl

instance RationalEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RationalEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow

instance RationalEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RationalEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RationalEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RationalEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RationalEmbeddingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RationalEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RationalEmbeddingTasteGate_single_carrier_alignment_fields
  field_faithful := RationalEmbeddingTasteGate_single_carrier_alignment_fields_faithful

theorem RationalEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RationalEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (RationalEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      RationalEmbeddingTasteGate_single_carrier_alignment_fields
          (RationalEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RationalEmbeddingTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.RationalEmbeddingUp
