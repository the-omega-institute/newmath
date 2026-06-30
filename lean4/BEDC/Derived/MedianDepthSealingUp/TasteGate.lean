import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MedianDepthSealingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MedianDepthSealingUp : Type where
  | mk (W B V T A L E H C P N : BHist) : MedianDepthSealingUp
  deriving DecidableEq

def MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist h

def MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def MedianDepthSealingTasteGate_single_carrier_alignment_fields :
    MedianDepthSealingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MedianDepthSealingUp.mk w b v t a l e h c p n =>
      [w, b, v, t, a, l, e, h, c, p, n]

def MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow :
    MedianDepthSealingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (MedianDepthSealingTasteGate_single_carrier_alignment_fields x).map
        MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist

private def MedianDepthSealingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MedianDepthSealingTasteGate_single_carrier_alignment_eventAt index rest

def MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MedianDepthSealingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MedianDepthSealingUp.mk
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 0 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 1 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 2 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 3 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 4 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 5 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 6 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 7 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 8 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 9 ef))
        (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
          (MedianDepthSealingTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem MedianDepthSealingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MedianDepthSealingUp,
      MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow
          (MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk w b v t a l e h c p n =>
      change
        some
            (MedianDepthSealingUp.mk
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist w))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist b))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist v))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist t))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist a))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist l))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist e))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist h))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist c))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist p))
              (MedianDepthSealingTasteGate_single_carrier_alignment_decodeBHist
                (MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist n))) =
          some (MedianDepthSealingUp.mk w b v t a l e h c p n)
      rw [MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode w,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode b,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode v,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode t,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode a,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode l,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode e,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode h,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode c,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode p,
        MedianDepthSealingTasteGate_single_carrier_alignment_decode_encode n]

private theorem MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MedianDepthSealingUp} :
    MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow x =
        MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow
          (MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow x) =
        MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow
          (MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MedianDepthSealingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MedianDepthSealingTasteGate_single_carrier_alignment_round_trip y)))

private theorem MedianDepthSealingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MedianDepthSealingUp,
      MedianDepthSealingTasteGate_single_carrier_alignment_fields x =
          MedianDepthSealingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk w₁ b₁ v₁ t₁ a₁ l₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk w₂ b₂ v₂ t₂ a₂ l₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance MedianDepthSealingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier MedianDepthSealingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow

instance MedianDepthSealingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate MedianDepthSealingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MedianDepthSealingTasteGate_single_carrier_alignment_fromEventFlow
          (MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact MedianDepthSealingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MedianDepthSealingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance MedianDepthSealingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful MedianDepthSealingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MedianDepthSealingTasteGate_single_carrier_alignment_fields
  field_faithful := MedianDepthSealingTasteGate_single_carrier_alignment_fields_faithful

instance MedianDepthSealingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial MedianDepthSealingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MedianDepthSealingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MedianDepthSealingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MedianDepthSealingTasteGate_single_carrier_alignment :
    (∀ w b v t a l e h c p n : BHist,
      MedianDepthSealingTasteGate_single_carrier_alignment_fields
          (MedianDepthSealingUp.mk w b v t a l e h c p n) =
        [w, b, v, t, a, l, e, h, c, p, n]) ∧
      MedianDepthSealingTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro w b v t a l e h c p n
    rfl
  · rfl

end BEDC.Derived.MedianDepthSealingUp
