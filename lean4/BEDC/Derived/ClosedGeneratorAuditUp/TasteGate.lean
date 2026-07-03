import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedGeneratorAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedGeneratorAuditUp : Type where
  | mk (T K R S A H C P N : BHist) : ClosedGeneratorAuditUp
  deriving DecidableEq

def closedGeneratorAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedGeneratorAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedGeneratorAuditEncodeBHist h

def closedGeneratorAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedGeneratorAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedGeneratorAuditDecodeBHist tail)

private theorem ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedGeneratorAuditFields : ClosedGeneratorAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedGeneratorAuditUp.mk T K R S A H C P N => [T, K, R, S, A, H, C, P, N]

def closedGeneratorAuditToEventFlow : ClosedGeneratorAuditUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedGeneratorAuditFields x).map closedGeneratorAuditEncodeBHist

private def closedGeneratorAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedGeneratorAuditEventAtDefault index rest

def closedGeneratorAuditFromEventFlow : EventFlow → Option ClosedGeneratorAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ClosedGeneratorAuditUp.mk
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 0 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 1 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 2 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 3 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 4 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 5 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 6 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 7 ef))
        (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEventAtDefault 8 ef)))

private theorem ClosedGeneratorAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedGeneratorAuditUp,
      closedGeneratorAuditFromEventFlow (closedGeneratorAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T K R S A H C P N =>
      change
        some
          (ClosedGeneratorAuditUp.mk
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist T))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist K))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist R))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist S))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist A))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist H))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist C))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist P))
            (closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist N))) =
          some (ClosedGeneratorAuditUp.mk T K R S A H C P N)
      rw [ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode T,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode K,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode R,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode S,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode A,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode H,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode C,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode P,
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode N]

theorem ClosedGeneratorAuditTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : ClosedGeneratorAuditUp} :
    closedGeneratorAuditToEventFlow x = closedGeneratorAuditToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = closedGeneratorAuditFromEventFlow (closedGeneratorAuditToEventFlow x) :=
        (ClosedGeneratorAuditTasteGate_single_carrier_alignment_round_trip x).symm
      _ = closedGeneratorAuditFromEventFlow (closedGeneratorAuditToEventFlow y) :=
        congrArg closedGeneratorAuditFromEventFlow hxy
      _ = some y := ClosedGeneratorAuditTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem ClosedGeneratorAuditTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ClosedGeneratorAuditUp, closedGeneratorAuditFields x = closedGeneratorAuditFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ K₁ R₁ S₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ K₂ R₂ S₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance closedGeneratorAuditBHistCarrier :
    BHistCarrier ClosedGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedGeneratorAuditToEventFlow
  fromEventFlow := closedGeneratorAuditFromEventFlow

instance closedGeneratorAuditChapterTasteGate :
    ChapterTasteGate ClosedGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedGeneratorAuditFromEventFlow (closedGeneratorAuditToEventFlow x) = some x
    exact ClosedGeneratorAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedGeneratorAuditTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

instance closedGeneratorAuditFieldFaithful :
    FieldFaithful ClosedGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedGeneratorAuditFields
  field_faithful := ClosedGeneratorAuditTasteGate_single_carrier_alignment_fields_faithful

instance closedGeneratorAuditNontrivial : Nontrivial ClosedGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedGeneratorAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedGeneratorAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ClosedGeneratorAuditTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ClosedGeneratorAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedGeneratorAuditChapterTasteGate

theorem ClosedGeneratorAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedGeneratorAuditDecodeBHist (closedGeneratorAuditEncodeBHist h) = h) ∧
      (∀ x : ClosedGeneratorAuditUp,
        closedGeneratorAuditFromEventFlow (closedGeneratorAuditToEventFlow x) = some x) ∧
        (∀ x y : ClosedGeneratorAuditUp,
          closedGeneratorAuditToEventFlow x = closedGeneratorAuditToEventFlow y -> x = y) ∧
          closedGeneratorAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨ClosedGeneratorAuditTasteGate_single_carrier_alignment_decode_encode,
      ClosedGeneratorAuditTasteGate_single_carrier_alignment_round_trip,
      fun x y hxy =>
        ClosedGeneratorAuditTasteGate_single_carrier_alignment_ToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.ClosedGeneratorAuditUp
