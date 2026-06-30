import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompleteRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompleteRealUp : Type where
  | mk (D W R E S F H C P N : BHist) : BishopCompleteRealUp
  deriving DecidableEq

def bishopCompleteRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompleteRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompleteRealEncodeBHist h

def bishopCompleteRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompleteRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompleteRealDecodeBHist tail)

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompleteRealFields : BishopCompleteRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompleteRealUp.mk D W R E S F H C P N => [D, W, R, E, S, F, H, C, P, N]

def bishopCompleteRealToEventFlow : BishopCompleteRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompleteRealFields x).map bishopCompleteRealEncodeBHist

private def bishopCompleteRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompleteRealEventAt index rest

def bishopCompleteRealFromEventFlow : EventFlow → Option BishopCompleteRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopCompleteRealUp.mk
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 0 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 1 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 2 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 3 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 4 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 5 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 6 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 7 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 8 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 9 ef)))

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_round_trip
    (x : BishopCompleteRealUp) :
    bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W R E S F H C P N =>
      change
        some
          (BishopCompleteRealUp.mk
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist D))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist W))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist R))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist E))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist S))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist F))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist H))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist C))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist P))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist N))) =
          some (BishopCompleteRealUp.mk D W R E S F H C P N)
      rw [BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode D,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode W,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode R,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode E,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode S,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode F,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode H,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode C,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode P,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompleteRealUp} :
    bishopCompleteRealToEventFlow x = bishopCompleteRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) =
        bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow y) :=
    congrArg bishopCompleteRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompleteRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopCompleteRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopCompleteRealUp, bishopCompleteRealFields x = bishopCompleteRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ R₁ E₁ S₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ R₂ E₂ S₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopCompleteRealBHistCarrier : BHistCarrier BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompleteRealToEventFlow
  fromEventFlow := bishopCompleteRealFromEventFlow

instance bishopCompleteRealChapterTasteGate : ChapterTasteGate BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) = some x
    exact BishopCompleteRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCompleteRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopCompleteRealFieldFaithful : FieldFaithful BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompleteRealFields
  field_faithful := BishopCompleteRealTasteGate_single_carrier_alignment_fields_faithful

instance bishopCompleteRealNontrivial : Nontrivial BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompleteRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCompleteRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BishopCompleteRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BishopCompleteRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompleteRealChapterTasteGate

theorem BishopCompleteRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopCompleteRealUp) ∧
      Nonempty (FieldFaithful BishopCompleteRealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopCompleteRealUp) ∧
          (∀ h : BHist, bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist h) = h) ∧
            (∀ x : BishopCompleteRealUp,
              bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) = some x) ∧
              (∀ x y : BishopCompleteRealUp,
                bishopCompleteRealToEventFlow x = bishopCompleteRealToEventFlow y -> x = y) ∧
                bishopCompleteRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨bishopCompleteRealChapterTasteGate⟩,
      ⟨bishopCompleteRealFieldFaithful⟩,
      ⟨bishopCompleteRealNontrivial⟩,
      BishopCompleteRealTasteGate_single_carrier_alignment_decode_encode,
      BishopCompleteRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BishopCompleteRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopCompleteRealUp.TasteGate
