import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TubeLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TubeLemmaUp : Type where
  | mk (X Y K O U V F H C P N : BHist) : TubeLemmaUp
  deriving DecidableEq

def tubeLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tubeLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tubeLemmaEncodeBHist h

def tubeLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tubeLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tubeLemmaDecodeBHist tail)

private theorem tubeLemma_decode_encode_bhist :
    ∀ h : BHist, tubeLemmaDecodeBHist (tubeLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tubeLemmaFields : TubeLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TubeLemmaUp.mk X Y K O U V F H C P N => [X, Y, K, O, U, V, F, H, C, P, N]

def tubeLemmaToEventFlow : TubeLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tubeLemmaFields x).map tubeLemmaEncodeBHist

private def tubeLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tubeLemmaEventAtDefault index rest

def tubeLemmaFromEventFlow (ef : EventFlow) : Option TubeLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TubeLemmaUp.mk
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 0 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 1 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 2 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 3 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 4 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 5 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 6 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 7 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 8 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 9 ef))
      (tubeLemmaDecodeBHist (tubeLemmaEventAtDefault 10 ef)))

private theorem tubeLemma_round_trip :
    ∀ x : TubeLemmaUp, tubeLemmaFromEventFlow (tubeLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y K O U V F H C P N =>
      change
        some
          (TubeLemmaUp.mk
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist X))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist Y))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist K))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist O))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist U))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist V))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist F))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist H))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist C))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist P))
            (tubeLemmaDecodeBHist (tubeLemmaEncodeBHist N))) =
          some (TubeLemmaUp.mk X Y K O U V F H C P N)
      rw [tubeLemma_decode_encode_bhist X,
        tubeLemma_decode_encode_bhist Y,
        tubeLemma_decode_encode_bhist K,
        tubeLemma_decode_encode_bhist O,
        tubeLemma_decode_encode_bhist U,
        tubeLemma_decode_encode_bhist V,
        tubeLemma_decode_encode_bhist F,
        tubeLemma_decode_encode_bhist H,
        tubeLemma_decode_encode_bhist C,
        tubeLemma_decode_encode_bhist P,
        tubeLemma_decode_encode_bhist N]

private theorem tubeLemmaToEventFlow_injective {x y : TubeLemmaUp} :
    tubeLemmaToEventFlow x = tubeLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tubeLemmaFromEventFlow (tubeLemmaToEventFlow x) =
        tubeLemmaFromEventFlow (tubeLemmaToEventFlow y) :=
    congrArg tubeLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tubeLemma_round_trip x).symm
      (Eq.trans hread (tubeLemma_round_trip y)))

private theorem tubeLemma_field_faithful :
    ∀ x y : TubeLemmaUp, tubeLemmaFields x = tubeLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ K₁ O₁ U₁ V₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ K₂ O₂ U₂ V₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance tubeLemmaBHistCarrier : BHistCarrier TubeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tubeLemmaToEventFlow
  fromEventFlow := tubeLemmaFromEventFlow

instance tubeLemmaChapterTasteGate : ChapterTasteGate TubeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tubeLemmaFromEventFlow (tubeLemmaToEventFlow x) = some x
    exact tubeLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tubeLemmaToEventFlow_injective heq)

instance tubeLemmaFieldFaithful : FieldFaithful TubeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tubeLemmaFields
  field_faithful := tubeLemma_field_faithful

instance tubeLemmaNontrivial : Nontrivial TubeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TubeLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TubeLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TubeLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tubeLemmaChapterTasteGate

theorem TubeLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, tubeLemmaDecodeBHist (tubeLemmaEncodeBHist h) = h) ∧
      (∀ x : TubeLemmaUp, tubeLemmaFromEventFlow (tubeLemmaToEventFlow x) = some x) ∧
        (∀ x y : TubeLemmaUp,
          tubeLemmaToEventFlow x = tubeLemmaToEventFlow y → x = y) ∧
          tubeLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨tubeLemma_decode_encode_bhist,
      ⟨tubeLemma_round_trip,
        ⟨fun _x _y heq => tubeLemmaToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.TubeLemmaUp
