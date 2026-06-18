import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChannelTerminationHaltingBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChannelTerminationHaltingBoundaryUp : Type where
  | mk (S E B D L R F H C P N : BHist) : ChannelTerminationHaltingBoundaryUp
  deriving DecidableEq

def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist h

def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields :
    ChannelTerminationHaltingBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChannelTerminationHaltingBoundaryUp.mk s e b d l r f h c p n =>
      [s, e, b, d, l, r, f, h, c, p, n]

def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow :
    ChannelTerminationHaltingBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields x).map
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist

private def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt index rest

def ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ChannelTerminationHaltingBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ChannelTerminationHaltingBoundaryUp.mk
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 0 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 1 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 2 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 3 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 4 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 5 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 6 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 7 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 8 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 9 ef))
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChannelTerminationHaltingBoundaryUp,
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk s e b d l r f h c p n =>
      change
        some
            (ChannelTerminationHaltingBoundaryUp.mk
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist s))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist e))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist b))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist d))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist l))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist r))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist f))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist h))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist c))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist p))
              (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist n))) =
          some (ChannelTerminationHaltingBoundaryUp.mk s e b d l r f h c p n)
      rw [ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode s,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode e,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode b,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode d,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode l,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode r,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode f,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode h,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode c,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode p,
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_decode_encode n]

private theorem ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChannelTerminationHaltingBoundaryUp} :
    ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow x =
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ChannelTerminationHaltingBoundaryUp,
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields x =
          ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s₁ e₁ b₁ d₁ l₁ r₁ f₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk s₂ e₂ b₂ d₂ l₂ r₂ f₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ChannelTerminationHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow

instance ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ChannelTerminationHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful ChannelTerminationHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields
  field_faithful :=
    ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields_faithful

instance ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial ChannelTerminationHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChannelTerminationHaltingBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChannelTerminationHaltingBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment :
    (∀ s e b d l r f h c p n : BHist,
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_fields
          (ChannelTerminationHaltingBoundaryUp.mk s e b d l r f h c p n) =
        [s, e, b, d, l, r, f, h, c, p, n]) ∧
      ChannelTerminationHaltingBoundaryTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro s e b d l r f h c p n
    rfl
  · rfl

end BEDC.Derived.ChannelTerminationHaltingBoundaryUp
