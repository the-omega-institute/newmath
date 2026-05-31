import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanSpaceUp : Type where
  | mk (S T B L C Q H R P N : BHist) : FanSpaceUp
  deriving DecidableEq

def fanSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanSpaceEncodeBHist h

def fanSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanSpaceDecodeBHist tail)

private theorem fanSpace_decode_encode :
    ∀ h : BHist, fanSpaceDecodeBHist (fanSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fanSpaceFields : FanSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanSpaceUp.mk S T B L C Q H R P N => [S, T, B, L, C, Q, H, R, P, N]

def fanSpaceToEventFlow : FanSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fanSpaceFields x).map fanSpaceEncodeBHist

private def FanSpaceTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => FanSpaceTasteGate_single_carrier_alignment_eventAt index rest

def fanSpaceFromEventFlow (ef : EventFlow) : Option FanSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FanSpaceUp.mk
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (fanSpaceDecodeBHist (FanSpaceTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem FanSpaceTasteGate_single_carrier_alignment_round_trip
    (x : FanSpaceUp) :
    fanSpaceFromEventFlow (fanSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T B L C Q H R P N =>
      change
        some
            (FanSpaceUp.mk
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist S))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist T))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist B))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist L))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist C))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist Q))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist H))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist R))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist P))
              (fanSpaceDecodeBHist (fanSpaceEncodeBHist N))) =
          some (FanSpaceUp.mk S T B L C Q H R P N)
      rw [fanSpace_decode_encode S,
        fanSpace_decode_encode T,
        fanSpace_decode_encode B,
        fanSpace_decode_encode L,
        fanSpace_decode_encode C,
        fanSpace_decode_encode Q,
        fanSpace_decode_encode H,
        fanSpace_decode_encode R,
        fanSpace_decode_encode P,
        fanSpace_decode_encode N]

private theorem FanSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FanSpaceUp} :
    fanSpaceToEventFlow x = fanSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = fanSpaceFromEventFlow (fanSpaceToEventFlow x) :=
        (FanSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      _ = fanSpaceFromEventFlow (fanSpaceToEventFlow y) :=
        congrArg fanSpaceFromEventFlow hxy
      _ = some y := FanSpaceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem fanSpace_field_faithful :
    ∀ x y : FanSpaceUp, fanSpaceFields x = fanSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ T₁ B₁ L₁ C₁ Q₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ B₂ L₂ C₂ Q₂ H₂ R₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hT tail1
          injection tail1 with hB tail2
          injection tail2 with hL tail3
          injection tail3 with hC tail4
          injection tail4 with hQ tail5
          injection tail5 with hH tail6
          injection tail6 with hR tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hT
          subst hB
          subst hL
          subst hC
          subst hQ
          subst hH
          subst hR
          subst hP
          subst hN
          rfl

instance fanSpaceBHistCarrier : BHistCarrier FanSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanSpaceToEventFlow
  fromEventFlow := fanSpaceFromEventFlow

instance fanSpaceChapterTasteGate : ChapterTasteGate FanSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanSpaceFromEventFlow (fanSpaceToEventFlow x) = some x
    exact FanSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FanSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fanSpaceFieldFaithful : FieldFaithful FanSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fanSpaceFields
  field_faithful := fanSpace_field_faithful

instance fanSpaceNontrivial : BEDC.Meta.TasteGate.Nontrivial FanSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FanSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FanSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FanSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanSpaceChapterTasteGate

theorem FanSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, fanSpaceDecodeBHist (fanSpaceEncodeBHist h) = h) ∧
      (∀ x : FanSpaceUp, fanSpaceFromEventFlow (fanSpaceToEventFlow x) = some x) ∧
        (∀ x y : FanSpaceUp, fanSpaceToEventFlow x = fanSpaceToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate FanSpaceUp) ∧
            (∀ x y : FanSpaceUp, fanSpaceFields x = fanSpaceFields y → x = y) ∧
              (∀ x : FanSpaceUp, ∃ h : BHist, List.Mem h (fanSpaceFields x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨fanSpace_decode_encode,
      FanSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => FanSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      ⟨fanSpaceChapterTasteGate⟩,
      fanSpace_field_faithful,
      by
        intro x
        cases x with
        | mk S T B L C Q H R P N =>
            exact ⟨S, List.Mem.head _⟩⟩

end BEDC.Derived.FanSpaceUp.TasteGate
