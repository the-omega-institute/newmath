import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanTheoremUp : Type where
  | mk (T B D W H C P N : BHist) : FanTheoremUp
  deriving DecidableEq

def FanTheoremTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FanTheoremTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FanTheoremTasteGate_single_carrier_alignment_encodeBHist h

def FanTheoremTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FanTheoremTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FanTheoremTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FanTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FanTheoremTasteGate_single_carrier_alignment_decodeBHist
        (FanTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FanTheoremTasteGate_single_carrier_alignment_fields :
    FanTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanTheoremUp.mk T B D W H C P N => [T, B, D, W, H, C, P, N]

def FanTheoremTasteGate_single_carrier_alignment_toEventFlow :
    FanTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b1, BMark.b0, BMark.b0] ::
        (FanTheoremTasteGate_single_carrier_alignment_fields x).map
          FanTheoremTasteGate_single_carrier_alignment_encodeBHist

private def FanTheoremTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      FanTheoremTasteGate_single_carrier_alignment_event_at index rest

def FanTheoremTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option FanTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [BMark.b1, BMark.b1, BMark.b0, BMark.b0] :: rows =>
      some
        (FanTheoremUp.mk
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 0 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 1 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 2 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 3 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 4 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 5 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 6 rows))
          (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
            (FanTheoremTasteGate_single_carrier_alignment_event_at 7 rows)))
  | _ => none

private theorem FanTheoremTasteGate_single_carrier_alignment_round_trip
    (x : FanTheoremUp) :
    FanTheoremTasteGate_single_carrier_alignment_fromEventFlow
      (FanTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T B D W H C P N =>
      change
        some
          (FanTheoremUp.mk
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist T))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist B))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist D))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist W))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist H))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist C))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist P))
            (FanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FanTheoremTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (FanTheoremUp.mk T B D W H C P N)
      rw [FanTheoremTasteGate_single_carrier_alignment_decode_encode T,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode B,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode D,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode W,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode H,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode C,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode P,
        FanTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem FanTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FanTheoremUp} :
    FanTheoremTasteGate_single_carrier_alignment_toEventFlow x =
      FanTheoremTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FanTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (FanTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        FanTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (FanTheoremTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FanTheoremTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FanTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FanTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem FanTheoremTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FanTheoremUp,
      FanTheoremTasteGate_single_carrier_alignment_fields x =
        FanTheoremTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ B₁ D₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ B₂ D₂ W₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance FanTheoremTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FanTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FanTheoremTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FanTheoremTasteGate_single_carrier_alignment_fromEventFlow

instance FanTheoremTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FanTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FanTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (FanTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact FanTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FanTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance FanTheoremTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful FanTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := FanTheoremTasteGate_single_carrier_alignment_fields
  field_faithful := FanTheoremTasteGate_single_carrier_alignment_fields_faithful

def FanTheoremTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FanTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FanTheoremTasteGate_single_carrier_alignment_ChapterTasteGate

theorem FanTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      FanTheoremTasteGate_single_carrier_alignment_decodeBHist
        (FanTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      FanTheoremTasteGate_single_carrier_alignment_fields
          (FanTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] ∧
      FanTheoremTasteGate_single_carrier_alignment_toEventFlow
          (FanTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b1, BMark.b0, BMark.b0], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FanTheoremTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.FanTheoremUp
