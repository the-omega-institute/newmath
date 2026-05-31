import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteChoiceUp : Type where
  | mk (I O B L W R S H C P N : BHist) : FiniteChoiceUp

def finiteChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteChoiceEncodeBHist h

def finiteChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteChoiceDecodeBHist tail)

private theorem FiniteChoiceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteChoiceDecodeBHist (finiteChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteChoiceToEventFlow : FiniteChoiceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteChoiceUp.mk I O B L W R S H C P N =>
      [finiteChoiceEncodeBHist I,
        finiteChoiceEncodeBHist O,
        finiteChoiceEncodeBHist B,
        finiteChoiceEncodeBHist L,
        finiteChoiceEncodeBHist W,
        finiteChoiceEncodeBHist R,
        finiteChoiceEncodeBHist S,
        finiteChoiceEncodeBHist H,
        finiteChoiceEncodeBHist C,
        finiteChoiceEncodeBHist P,
        finiteChoiceEncodeBHist N]

private def finiteChoiceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteChoiceEventAtDefault index rest

def finiteChoiceFromEventFlow (ef : EventFlow) : Option FiniteChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteChoiceUp.mk
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 0 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 1 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 2 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 3 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 4 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 5 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 6 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 7 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 8 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 9 ef))
      (finiteChoiceDecodeBHist (finiteChoiceEventAtDefault 10 ef)))

private theorem FiniteChoiceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteChoiceUp,
      finiteChoiceFromEventFlow (finiteChoiceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I O B L W R S H C P N =>
      change
        some
          (FiniteChoiceUp.mk
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist I))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist O))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist B))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist L))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist W))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist R))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist S))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist H))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist C))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist P))
            (finiteChoiceDecodeBHist (finiteChoiceEncodeBHist N))) =
          some (FiniteChoiceUp.mk I O B L W R S H C P N)
      rw [FiniteChoiceTasteGate_single_carrier_alignment_decode_encode I,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode O,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode B,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode L,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode W,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode R,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode S,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode H,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode C,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode P,
        FiniteChoiceTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteChoiceUp} :
    finiteChoiceToEventFlow x = finiteChoiceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteChoiceFromEventFlow (finiteChoiceToEventFlow x) =
        finiteChoiceFromEventFlow (finiteChoiceToEventFlow y) :=
    congrArg finiteChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteChoiceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteChoiceTasteGate_single_carrier_alignment_round_trip y)))

instance finiteChoiceBHistCarrier : BHistCarrier FiniteChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteChoiceToEventFlow
  fromEventFlow := finiteChoiceFromEventFlow

instance finiteChoiceChapterTasteGate : ChapterTasteGate FiniteChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteChoiceFromEventFlow (finiteChoiceToEventFlow x) = some x
    exact FiniteChoiceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteChoiceChapterTasteGate

theorem FiniteChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteChoiceDecodeBHist (finiteChoiceEncodeBHist h) = h) ∧
      (∀ x : FiniteChoiceUp,
        finiteChoiceFromEventFlow (finiteChoiceToEventFlow x) = some x) ∧
        (∀ x y : FiniteChoiceUp,
          finiteChoiceToEventFlow x = finiteChoiceToEventFlow y → x = y) ∧
          finiteChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FiniteChoiceTasteGate_single_carrier_alignment_decode_encode,
      FiniteChoiceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteChoiceUp
