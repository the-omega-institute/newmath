import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireCategoryChoiceFreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireCategoryChoiceFreeUp : Type where
  | mk (B M W R S K H C P N : BHist) : BaireCategoryChoiceFreeUp
  deriving DecidableEq

def baireCategoryChoiceFreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireCategoryChoiceFreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireCategoryChoiceFreeEncodeBHist h

def baireCategoryChoiceFreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireCategoryChoiceFreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireCategoryChoiceFreeDecodeBHist tail)

private theorem BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireCategoryChoiceFreeDecodeBHist
      (baireCategoryChoiceFreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireCategoryChoiceFreeFields : BaireCategoryChoiceFreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireCategoryChoiceFreeUp.mk B M W R S K H C P N => [B, M, W, R, S, K, H, C, P, N]

def baireCategoryChoiceFreeToEventFlow : BaireCategoryChoiceFreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireCategoryChoiceFreeFields x).map baireCategoryChoiceFreeEncodeBHist

private def baireCategoryChoiceFreeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireCategoryChoiceFreeRawAt index rest

private def baireCategoryChoiceFreeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => baireCategoryChoiceFreeLengthEq index rest

def baireCategoryChoiceFreeFromEventFlow : EventFlow → Option BaireCategoryChoiceFreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match baireCategoryChoiceFreeLengthEq 10 flow with
      | true =>
          some
            (BaireCategoryChoiceFreeUp.mk
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 0 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 1 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 2 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 3 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 4 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 5 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 6 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 7 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 8 flow))
              (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeRawAt 9 flow)))
      | false => none

private theorem baireCategoryChoiceFree_round_trip :
    ∀ x : BaireCategoryChoiceFreeUp,
      baireCategoryChoiceFreeFromEventFlow (baireCategoryChoiceFreeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M W R S K H C P N =>
      change
        some
          (BaireCategoryChoiceFreeUp.mk
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist B))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist M))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist W))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist R))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist S))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist K))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist H))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist C))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist P))
            (baireCategoryChoiceFreeDecodeBHist (baireCategoryChoiceFreeEncodeBHist N))) =
          some (BaireCategoryChoiceFreeUp.mk B M W R S K H C P N)
      rw [BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode B,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode M,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode W,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode R,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode S,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode K,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode H,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode C,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode P,
        BaireCategoryChoiceFreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem baireCategoryChoiceFreeToEventFlow_injective
    {x y : BaireCategoryChoiceFreeUp} :
    baireCategoryChoiceFreeToEventFlow x = baireCategoryChoiceFreeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireCategoryChoiceFreeFromEventFlow (baireCategoryChoiceFreeToEventFlow x) =
        baireCategoryChoiceFreeFromEventFlow (baireCategoryChoiceFreeToEventFlow y) :=
    congrArg baireCategoryChoiceFreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (baireCategoryChoiceFree_round_trip x).symm
      (Eq.trans hread (baireCategoryChoiceFree_round_trip y)))

instance baireCategoryChoiceFreeBHistCarrier : BHistCarrier BaireCategoryChoiceFreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireCategoryChoiceFreeToEventFlow
  fromEventFlow := baireCategoryChoiceFreeFromEventFlow

instance baireCategoryChoiceFreeChapterTasteGate :
    ChapterTasteGate BaireCategoryChoiceFreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      baireCategoryChoiceFreeFromEventFlow (baireCategoryChoiceFreeToEventFlow x) =
        some x
    exact baireCategoryChoiceFree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (baireCategoryChoiceFreeToEventFlow_injective heq)

namespace TasteGate

theorem BaireCategoryChoiceFreeTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BaireCategoryChoiceFreeUp) ∧
      Nonempty (ChapterTasteGate BaireCategoryChoiceFreeUp) ∧
        (∀ x : BaireCategoryChoiceFreeUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro baireCategoryChoiceFreeBHistCarrier,
      Nonempty.intro baireCategoryChoiceFreeChapterTasteGate,
      ChapterTasteGate.round_trip⟩

end TasteGate

end BEDC.Derived.BaireCategoryChoiceFreeUp
