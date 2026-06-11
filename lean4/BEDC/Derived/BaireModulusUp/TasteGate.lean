import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireModulusUp : Type where
  | mk (B S W mu R H C P N : BHist) : BaireModulusUp
  deriving DecidableEq

def BaireModulusTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BaireModulusTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BaireModulusTasteGate_single_carrier_alignment_encodeBHist h

def BaireModulusTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BaireModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BaireModulusTasteGate_single_carrier_alignment_fields :
    BaireModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireModulusUp.mk B S W mu R H C P N => [B, S, W, mu, R, H, C, P, N]

def BaireModulusTasteGate_single_carrier_alignment_toEventFlow :
    BaireModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BaireModulusTasteGate_single_carrier_alignment_fields x).map
        BaireModulusTasteGate_single_carrier_alignment_encodeBHist

private def BaireModulusTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BaireModulusTasteGate_single_carrier_alignment_eventAtDefault index rest

def BaireModulusTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireModulusUp.mk
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
        (BaireModulusTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem BaireModulusTasteGate_single_carrier_alignment_round_trip
    (x : BaireModulusUp) :
    BaireModulusTasteGate_single_carrier_alignment_fromEventFlow
      (BaireModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B S W mu R H C P N =>
      change
        some
          (BaireModulusUp.mk
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist B))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist S))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist W))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist mu))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist R))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist H))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist C))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist P))
            (BaireModulusTasteGate_single_carrier_alignment_decodeBHist
              (BaireModulusTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BaireModulusUp.mk B S W mu R H C P N)
      rw [BaireModulusTasteGate_single_carrier_alignment_decode_encode B,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode S,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode W,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode mu,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode R,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode H,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode C,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode P,
        BaireModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireModulusTasteGate_single_carrier_alignment_injective
    {x y : BaireModulusUp} :
    BaireModulusTasteGate_single_carrier_alignment_toEventFlow x =
      BaireModulusTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BaireModulusTasteGate_single_carrier_alignment_fromEventFlow
          (BaireModulusTasteGate_single_carrier_alignment_toEventFlow x) =
        BaireModulusTasteGate_single_carrier_alignment_fromEventFlow
          (BaireModulusTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BaireModulusTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BaireModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BaireModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireModulusTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BaireModulusUp,
      BaireModulusTasteGate_single_carrier_alignment_fields x =
        BaireModulusTasteGate_single_carrier_alignment_fields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ S₁ W₁ mu₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ S₂ W₂ mu₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance BaireModulusTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BaireModulusTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BaireModulusTasteGate_single_carrier_alignment_fromEventFlow

instance BaireModulusTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BaireModulusTasteGate_single_carrier_alignment_fields
  field_faithful := BaireModulusTasteGate_single_carrier_alignment_field_faithful

instance BaireModulusTasteGate_single_carrier_alignment_Nontrivial :
    BEDC.Meta.TasteGate.Nontrivial BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BaireModulusTasteGate_single_carrier_alignment :
    ChapterTasteGate BaireModulusUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      BaireModulusTasteGate_single_carrier_alignment_fromEventFlow
        (BaireModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact BaireModulusTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (BaireModulusTasteGate_single_carrier_alignment_injective heq)

instance BaireModulusTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BaireModulusTasteGate_single_carrier_alignment

def BaireModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BaireModulusTasteGate_single_carrier_alignment

end BEDC.Derived.BaireModulusUp
