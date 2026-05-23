import BEDC.Derived.RealOscillationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealOscillationUp : Type where
  | mk (X O C S D W R H T P N : BHist) : RealOscillationUp
  deriving DecidableEq

def realOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realOscillationEncodeBHist h

def realOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realOscillationDecodeBHist tail)

private theorem RealOscillationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realOscillationDecodeBHist (realOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realOscillationFields : RealOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealOscillationUp.mk X O C S D W R H T P N => [X, O, C, S, D, W, R, H, T, P, N]

def realOscillationToEventFlow : RealOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realOscillationFields x).map realOscillationEncodeBHist

private def realOscillationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realOscillationEventAt index rest

def realOscillationFromEventFlow (ef : EventFlow) : Option RealOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealOscillationUp.mk
      (realOscillationDecodeBHist (realOscillationEventAt 0 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 1 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 2 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 3 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 4 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 5 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 6 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 7 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 8 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 9 ef))
      (realOscillationDecodeBHist (realOscillationEventAt 10 ef)))

private theorem RealOscillationTasteGate_single_carrier_alignment_round_trip
    (x : RealOscillationUp) :
    realOscillationFromEventFlow (realOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X O C S D W R H T P N =>
      change
        some
          (RealOscillationUp.mk
            (realOscillationDecodeBHist (realOscillationEncodeBHist X))
            (realOscillationDecodeBHist (realOscillationEncodeBHist O))
            (realOscillationDecodeBHist (realOscillationEncodeBHist C))
            (realOscillationDecodeBHist (realOscillationEncodeBHist S))
            (realOscillationDecodeBHist (realOscillationEncodeBHist D))
            (realOscillationDecodeBHist (realOscillationEncodeBHist W))
            (realOscillationDecodeBHist (realOscillationEncodeBHist R))
            (realOscillationDecodeBHist (realOscillationEncodeBHist H))
            (realOscillationDecodeBHist (realOscillationEncodeBHist T))
            (realOscillationDecodeBHist (realOscillationEncodeBHist P))
            (realOscillationDecodeBHist (realOscillationEncodeBHist N))) =
          some (RealOscillationUp.mk X O C S D W R H T P N)
      rw [RealOscillationTasteGate_single_carrier_alignment_decode_encode X,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode O,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode C,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode S,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode D,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode W,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode R,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode H,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode T,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode P,
        RealOscillationTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealOscillationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealOscillationUp} :
    realOscillationToEventFlow x = realOscillationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realOscillationFromEventFlow (realOscillationToEventFlow x) =
        realOscillationFromEventFlow (realOscillationToEventFlow y) :=
    congrArg realOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealOscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealOscillationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealOscillationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealOscillationUp,
      realOscillationFields x = realOscillationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ O₁ C₁ S₁ D₁ W₁ R₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk X₂ O₂ C₂ S₂ D₂ W₂ R₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance realOscillationBHistCarrier : BHistCarrier RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realOscillationToEventFlow
  fromEventFlow := realOscillationFromEventFlow

instance realOscillationChapterTasteGate : ChapterTasteGate RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realOscillationFromEventFlow (realOscillationToEventFlow x) = some x
    exact RealOscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealOscillationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realOscillationFieldFaithful : FieldFaithful RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realOscillationFields
  field_faithful := RealOscillationTasteGate_single_carrier_alignment_fields_faithful

instance realOscillationNontrivial : Nontrivial RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealOscillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealOscillationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist, realOscillationDecodeBHist (realOscillationEncodeBHist h) = h) ∧
      (∀ x : RealOscillationUp,
        realOscillationFromEventFlow (realOscillationToEventFlow x) = some x) ∧
        (∀ x y : RealOscillationUp,
          realOscillationToEventFlow x = realOscillationToEventFlow y → x = y) ∧
          realOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RealOscillationTasteGate_single_carrier_alignment_decode_encode,
      RealOscillationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealOscillationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealOscillationUp
