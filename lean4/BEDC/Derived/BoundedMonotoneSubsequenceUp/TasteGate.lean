import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedMonotoneSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedMonotoneSubsequenceUp : Type where
  | mk (S D I W R E H C P N : BHist) : BoundedMonotoneSubsequenceUp
  deriving DecidableEq

def boundedMonotoneSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedMonotoneSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedMonotoneSubsequenceEncodeBHist h

def boundedMonotoneSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedMonotoneSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedMonotoneSubsequenceDecodeBHist tail)

private theorem BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedMonotoneSubsequenceFields : BoundedMonotoneSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedMonotoneSubsequenceUp.mk S D I W R E H C P N => [S, D, I, W, R, E, H, C, P, N]

def boundedMonotoneSubsequenceToEventFlow : BoundedMonotoneSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedMonotoneSubsequenceUp.mk S D I W R E H C P N =>
      (boundedMonotoneSubsequenceFields
          (BoundedMonotoneSubsequenceUp.mk S D I W R E H C P N)).map
        boundedMonotoneSubsequenceEncodeBHist

private def boundedMonotoneSubsequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedMonotoneSubsequenceEventAt index rest

def boundedMonotoneSubsequenceFromEventFlow
    (ef : EventFlow) : Option BoundedMonotoneSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedMonotoneSubsequenceUp.mk
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 0 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 1 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 2 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 3 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 4 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 5 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 6 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 7 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 8 ef))
      (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEventAt 9 ef)))

private theorem BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedMonotoneSubsequenceUp,
      boundedMonotoneSubsequenceFromEventFlow (boundedMonotoneSubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D I W R E H C P N =>
      change
        some
          (BoundedMonotoneSubsequenceUp.mk
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist S))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist D))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist I))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist W))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist R))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist E))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist H))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist C))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist P))
            (boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist N))) =
          some (BoundedMonotoneSubsequenceUp.mk S D I W R E H C P N)
      rw [BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode S,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode D,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode I,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode W,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode R,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode E,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode H,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode C,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode P,
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedMonotoneSubsequenceUp} :
    boundedMonotoneSubsequenceToEventFlow x = boundedMonotoneSubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedMonotoneSubsequenceFromEventFlow (boundedMonotoneSubsequenceToEventFlow x) =
        boundedMonotoneSubsequenceFromEventFlow (boundedMonotoneSubsequenceToEventFlow y) :=
    congrArg boundedMonotoneSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BoundedMonotoneSubsequenceUp,
      boundedMonotoneSubsequenceFields x = boundedMonotoneSubsequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ D₁ I₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ I₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedMonotoneSubsequenceBHistCarrier :
    BHistCarrier BoundedMonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedMonotoneSubsequenceToEventFlow
  fromEventFlow := boundedMonotoneSubsequenceFromEventFlow

instance boundedMonotoneSubsequenceChapterTasteGate :
    ChapterTasteGate BoundedMonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedMonotoneSubsequenceFromEventFlow (boundedMonotoneSubsequenceToEventFlow x) =
        some x
    exact BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedMonotoneSubsequenceFieldFaithful :
    FieldFaithful BoundedMonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedMonotoneSubsequenceFields
  field_faithful := BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_fields_faithful

instance boundedMonotoneSubsequenceNontrivial :
    Nontrivial BoundedMonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedMonotoneSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedMonotoneSubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedMonotoneSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedMonotoneSubsequenceChapterTasteGate

theorem BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedMonotoneSubsequenceDecodeBHist (boundedMonotoneSubsequenceEncodeBHist h) = h) ∧
      (∀ x : BoundedMonotoneSubsequenceUp,
        boundedMonotoneSubsequenceFromEventFlow (boundedMonotoneSubsequenceToEventFlow x) =
          some x) ∧
        (∀ x y : BoundedMonotoneSubsequenceUp,
          boundedMonotoneSubsequenceToEventFlow x = boundedMonotoneSubsequenceToEventFlow y →
            x = y) ∧
          boundedMonotoneSubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_decode_encode,
      BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedMonotoneSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedMonotoneSubsequenceUp
