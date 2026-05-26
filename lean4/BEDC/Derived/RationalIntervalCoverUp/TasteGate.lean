import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalIntervalCoverUp : Type where
  | mk (I F R W H K P N : BHist) : RationalIntervalCoverUp
  deriving DecidableEq

def rationalIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalIntervalCoverEncodeBHist h

def rationalIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalIntervalCoverDecodeBHist tail)

private theorem RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def rationalIntervalCoverFields : RationalIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalIntervalCoverUp.mk I F R W H K P N => [I, F, R, W, H, K, P, N]

def rationalIntervalCoverToEventFlow : RationalIntervalCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalIntervalCoverFields x).map rationalIntervalCoverEncodeBHist

private def rationalIntervalCoverEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalIntervalCoverEventAt index rest

def rationalIntervalCoverFromEventFlow (ef : EventFlow) : Option RationalIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalIntervalCoverUp.mk
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 0 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 1 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 2 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 3 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 4 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 5 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 6 ef))
      (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEventAt 7 ef)))

private theorem RationalIntervalCoverTasteGate_single_carrier_alignment_round_trip
    (x : RationalIntervalCoverUp) :
    rationalIntervalCoverFromEventFlow (rationalIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F R W H K P N =>
      change
        some
          (RationalIntervalCoverUp.mk
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist I))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist F))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist R))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist W))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist H))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist K))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist P))
            (rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist N))) =
          some (RationalIntervalCoverUp.mk I F R W H K P N)
      rw [RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode I,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode F,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode R,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode W,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode H,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode K,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode P,
        RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem RationalIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalIntervalCoverUp} :
    rationalIntervalCoverToEventFlow x = rationalIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalIntervalCoverFromEventFlow (rationalIntervalCoverToEventFlow x) =
        rationalIntervalCoverFromEventFlow (rationalIntervalCoverToEventFlow y) :=
    congrArg rationalIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalIntervalCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RationalIntervalCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalIntervalCoverTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RationalIntervalCoverUp, rationalIntervalCoverFields x = rationalIntervalCoverFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ R₁ W₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk I₂ F₂ R₂ W₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance rationalIntervalCoverBHistCarrier : BHistCarrier RationalIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalIntervalCoverToEventFlow
  fromEventFlow := rationalIntervalCoverFromEventFlow

instance rationalIntervalCoverChapterTasteGate : ChapterTasteGate RationalIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalIntervalCoverFromEventFlow (rationalIntervalCoverToEventFlow x) = some x
    exact RationalIntervalCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalIntervalCoverFieldFaithful : FieldFaithful RationalIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalIntervalCoverFields
  field_faithful := RationalIntervalCoverTasteGate_single_carrier_alignment_fields_faithful

instance rationalIntervalCoverNontrivial : Nontrivial RationalIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalIntervalCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalIntervalCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RationalIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalIntervalCoverChapterTasteGate

theorem RationalIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, rationalIntervalCoverDecodeBHist (rationalIntervalCoverEncodeBHist h) = h) ∧
      (∀ x : RationalIntervalCoverUp,
        rationalIntervalCoverFromEventFlow (rationalIntervalCoverToEventFlow x) = some x) ∧
        (∀ x y : RationalIntervalCoverUp,
          rationalIntervalCoverToEventFlow x = rationalIntervalCoverToEventFlow y → x = y) ∧
          rationalIntervalCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RationalIntervalCoverTasteGate_single_carrier_alignment_decode_encode,
      RationalIntervalCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RationalIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RationalIntervalCoverUp
