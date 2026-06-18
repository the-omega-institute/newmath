import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireSpaceCompactOpenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireSpaceCompactOpenUp : Type where
  | mk (B O F W R E H C P N : BHist) : BaireSpaceCompactOpenUp
  deriving DecidableEq

def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist h

def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields :
    BaireSpaceCompactOpenUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireSpaceCompactOpenUp.mk b o f w r e h c p n => [b, o, f, w, r, e, h, c, p, n]

def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow :
    BaireSpaceCompactOpenUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields x).map
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist

private def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt index rest

def BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BaireSpaceCompactOpenUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BaireSpaceCompactOpenUp.mk
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 0 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 1 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 2 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 3 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 4 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 5 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 6 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 7 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 8 ef))
        (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem BaireSpaceCompactOpenTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BaireSpaceCompactOpenUp,
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk b o f w r e h c p n =>
      change
        some
            (BaireSpaceCompactOpenUp.mk
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist b))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist o))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist f))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist w))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist r))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist e))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist h))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist c))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist p))
              (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decodeBHist
                (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist n))) =
          some (BaireSpaceCompactOpenUp.mk b o f w r e h c p n)
      rw [BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode b,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode o,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode f,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode w,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode r,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode e,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode h,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode c,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode p,
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_decode_encode n]

private theorem BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireSpaceCompactOpenUp} :
    BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow x =
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow x) =
        BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BaireSpaceCompactOpenUp,
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields x =
          BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk b₁ o₁ f₁ w₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk b₂ o₂ f₂ w₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance BaireSpaceCompactOpenTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BaireSpaceCompactOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow

instance BaireSpaceCompactOpenTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BaireSpaceCompactOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fromEventFlow
          (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BaireSpaceCompactOpenTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireSpaceCompactOpenTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BaireSpaceCompactOpenTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BaireSpaceCompactOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields
  field_faithful := BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields_faithful

instance BaireSpaceCompactOpenTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial BaireSpaceCompactOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireSpaceCompactOpenUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireSpaceCompactOpenUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BaireSpaceCompactOpenTasteGate_single_carrier_alignment :
    (∀ b o f w r e h c p n : BHist,
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_fields
          (BaireSpaceCompactOpenUp.mk b o f w r e h c p n) =
        [b, o, f, w, r, e, h, c, p, n]) ∧
      BaireSpaceCompactOpenTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro b o f w r e h c p n
    rfl
  · rfl

end BEDC.Derived.BaireSpaceCompactOpenUp
