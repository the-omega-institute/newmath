import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalRealUp : Type where
  | mk (I B D E W R S H C P N : BHist) : NestedIntervalRealUp
  deriving DecidableEq

def nestedIntervalRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalRealEncodeBHist h

def nestedIntervalRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalRealDecodeBHist tail)

private theorem nestedIntervalReal_decode_encode :
    ∀ h : BHist, nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nestedIntervalRealFields : NestedIntervalRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalRealUp.mk I B D E W R S H C P N => [I, B, D, E, W, R, S, H, C, P, N]

def nestedIntervalRealToEventFlow : NestedIntervalRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedIntervalRealFields x).map nestedIntervalRealEncodeBHist

private def NestedIntervalRealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      NestedIntervalRealTasteGate_single_carrier_alignment_eventAt index rest

def nestedIntervalRealFromEventFlow (ef : EventFlow) : Option NestedIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalRealUp.mk
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 7 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 8 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 9 ef))
      (nestedIntervalRealDecodeBHist
        (NestedIntervalRealTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem NestedIntervalRealTasteGate_single_carrier_alignment_round_trip
    (x : NestedIntervalRealUp) :
    nestedIntervalRealFromEventFlow (nestedIntervalRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I B D E W R S H C P N =>
      change
        some
            (NestedIntervalRealUp.mk
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist I))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist B))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist D))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist E))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist W))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist R))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist S))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist H))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist C))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist P))
              (nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist N))) =
          some (NestedIntervalRealUp.mk I B D E W R S H C P N)
      rw [nestedIntervalReal_decode_encode I,
        nestedIntervalReal_decode_encode B,
        nestedIntervalReal_decode_encode D,
        nestedIntervalReal_decode_encode E,
        nestedIntervalReal_decode_encode W,
        nestedIntervalReal_decode_encode R,
        nestedIntervalReal_decode_encode S,
        nestedIntervalReal_decode_encode H,
        nestedIntervalReal_decode_encode C,
        nestedIntervalReal_decode_encode P,
        nestedIntervalReal_decode_encode N]

private theorem NestedIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedIntervalRealUp} :
    nestedIntervalRealToEventFlow x = nestedIntervalRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          nestedIntervalRealFromEventFlow (nestedIntervalRealToEventFlow x) :=
        (NestedIntervalRealTasteGate_single_carrier_alignment_round_trip x).symm
      _ = nestedIntervalRealFromEventFlow (nestedIntervalRealToEventFlow y) :=
        congrArg nestedIntervalRealFromEventFlow hxy
      _ = some y := NestedIntervalRealTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem nestedIntervalReal_field_faithful :
    ∀ x y : NestedIntervalRealUp, nestedIntervalRealFields x = nestedIntervalRealFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ B₁ D₁ E₁ W₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ B₂ D₂ E₂ W₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hB tail1
          injection tail1 with hD tail2
          injection tail2 with hE tail3
          injection tail3 with hW tail4
          injection tail4 with hR tail5
          injection tail5 with hS tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hI
          subst hB
          subst hD
          subst hE
          subst hW
          subst hR
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance nestedIntervalRealBHistCarrier : BHistCarrier NestedIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalRealToEventFlow
  fromEventFlow := nestedIntervalRealFromEventFlow

instance nestedIntervalRealChapterTasteGate : ChapterTasteGate NestedIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalRealFromEventFlow (nestedIntervalRealToEventFlow x) = some x
    exact NestedIntervalRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NestedIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedIntervalRealFieldFaithful : FieldFaithful NestedIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalRealFields
  field_faithful := nestedIntervalReal_field_faithful

instance nestedIntervalRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial NestedIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedIntervalRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalRealChapterTasteGate

theorem NestedIntervalRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedIntervalRealDecodeBHist (nestedIntervalRealEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalRealUp,
        nestedIntervalRealFromEventFlow (nestedIntervalRealToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalRealUp,
          nestedIntervalRealToEventFlow x = nestedIntervalRealToEventFlow y → x = y) ∧
          nestedIntervalRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨nestedIntervalReal_decode_encode,
      NestedIntervalRealTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => NestedIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.NestedIntervalRealUp.TasteGate
