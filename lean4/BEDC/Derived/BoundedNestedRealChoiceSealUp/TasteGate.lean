import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNestedRealChoiceSealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNestedRealChoiceSealUp : Type where
  | mk (I L C W R D E H T P N : BHist) : BoundedNestedRealChoiceSealUp
  deriving DecidableEq

def boundedNestedRealChoiceSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNestedRealChoiceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNestedRealChoiceSealEncodeBHist h

def boundedNestedRealChoiceSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNestedRealChoiceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNestedRealChoiceSealDecodeBHist tail)

private theorem boundedNestedRealChoiceSeal_decode_encode :
    ∀ h : BHist,
      boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedNestedRealChoiceSealFields : BoundedNestedRealChoiceSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNestedRealChoiceSealUp.mk I L C W R D E H T P N => [I, L, C, W, R, D, E, H, T, P, N]

def boundedNestedRealChoiceSealToEventFlow : BoundedNestedRealChoiceSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedNestedRealChoiceSealFields x).map boundedNestedRealChoiceSealEncodeBHist

private def boundedNestedRealChoiceSealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedNestedRealChoiceSealEventAt index rest

def boundedNestedRealChoiceSealFromEventFlow (ef : EventFlow) :
    Option BoundedNestedRealChoiceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedNestedRealChoiceSealUp.mk
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 0 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 1 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 2 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 3 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 4 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 5 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 6 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 7 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 8 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 9 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAt 10 ef)))

private theorem boundedNestedRealChoiceSeal_round_trip
    (x : BoundedNestedRealChoiceSealUp) :
    boundedNestedRealChoiceSealFromEventFlow
        (boundedNestedRealChoiceSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I L C W R D E H T P N =>
      change
        some
            (BoundedNestedRealChoiceSealUp.mk
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist I))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist L))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist C))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist W))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist R))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist D))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist E))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist H))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist T))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist P))
              (boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist N))) =
          some (BoundedNestedRealChoiceSealUp.mk I L C W R D E H T P N)
      rw [boundedNestedRealChoiceSeal_decode_encode I,
        boundedNestedRealChoiceSeal_decode_encode L,
        boundedNestedRealChoiceSeal_decode_encode C,
        boundedNestedRealChoiceSeal_decode_encode W,
        boundedNestedRealChoiceSeal_decode_encode R,
        boundedNestedRealChoiceSeal_decode_encode D,
        boundedNestedRealChoiceSeal_decode_encode E,
        boundedNestedRealChoiceSeal_decode_encode H,
        boundedNestedRealChoiceSeal_decode_encode T,
        boundedNestedRealChoiceSeal_decode_encode P,
        boundedNestedRealChoiceSeal_decode_encode N]

private theorem boundedNestedRealChoiceSealToEventFlow_injective
    {x y : BoundedNestedRealChoiceSealUp} :
    boundedNestedRealChoiceSealToEventFlow x =
        boundedNestedRealChoiceSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          boundedNestedRealChoiceSealFromEventFlow
            (boundedNestedRealChoiceSealToEventFlow x) :=
        (boundedNestedRealChoiceSeal_round_trip x).symm
      _ =
          boundedNestedRealChoiceSealFromEventFlow
            (boundedNestedRealChoiceSealToEventFlow y) :=
        congrArg boundedNestedRealChoiceSealFromEventFlow hxy
      _ = some y := boundedNestedRealChoiceSeal_round_trip y
  exact Option.some.inj optionEq

private theorem boundedNestedRealChoiceSeal_field_faithful :
    ∀ x y : BoundedNestedRealChoiceSealUp,
      boundedNestedRealChoiceSealFields x = boundedNestedRealChoiceSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ L₁ C₁ W₁ R₁ D₁ E₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk I₂ L₂ C₂ W₂ R₂ D₂ E₂ H₂ T₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hL tail1
          injection tail1 with hC tail2
          injection tail2 with hW tail3
          injection tail3 with hR tail4
          injection tail4 with hD tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hT tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hI
          subst hL
          subst hC
          subst hW
          subst hR
          subst hD
          subst hE
          subst hH
          subst hT
          subst hP
          subst hN
          rfl

instance boundedNestedRealChoiceSealBHistCarrier :
    BHistCarrier BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNestedRealChoiceSealToEventFlow
  fromEventFlow := boundedNestedRealChoiceSealFromEventFlow

instance boundedNestedRealChoiceSealChapterTasteGate :
    ChapterTasteGate BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedNestedRealChoiceSealFromEventFlow
        (boundedNestedRealChoiceSealToEventFlow x) = some x
    exact boundedNestedRealChoiceSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedNestedRealChoiceSealToEventFlow_injective heq)

instance boundedNestedRealChoiceSealFieldFaithful :
    FieldFaithful BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedNestedRealChoiceSealFields
  field_faithful := boundedNestedRealChoiceSeal_field_faithful

instance boundedNestedRealChoiceSealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedNestedRealChoiceSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedNestedRealChoiceSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def boundedNestedRealChoiceSeal_taste_gate :
    ChapterTasteGate BoundedNestedRealChoiceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedNestedRealChoiceSealChapterTasteGate

theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedNestedRealChoiceSealUp) ∧
      Nonempty (FieldFaithful BoundedNestedRealChoiceSealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedNestedRealChoiceSealUp) ∧
          (∀ h : BHist,
            boundedNestedRealChoiceSealDecodeBHist
              (boundedNestedRealChoiceSealEncodeBHist h) = h) ∧
            (∀ x : BoundedNestedRealChoiceSealUp,
              boundedNestedRealChoiceSealFromEventFlow
                (boundedNestedRealChoiceSealToEventFlow x) = some x) ∧
              (∀ x y : BoundedNestedRealChoiceSealUp,
                boundedNestedRealChoiceSealToEventFlow x =
                    boundedNestedRealChoiceSealToEventFlow y →
                  x = y) ∧
                boundedNestedRealChoiceSealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨boundedNestedRealChoiceSealChapterTasteGate⟩,
      ⟨boundedNestedRealChoiceSealFieldFaithful⟩,
      ⟨boundedNestedRealChoiceSealNontrivial⟩,
      boundedNestedRealChoiceSeal_decode_encode,
      boundedNestedRealChoiceSeal_round_trip,
      fun _ _ heq => boundedNestedRealChoiceSealToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BoundedNestedRealChoiceSealUp.TasteGate
