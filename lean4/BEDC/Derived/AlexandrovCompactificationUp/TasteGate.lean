import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlexandrovCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlexandrovCompactificationUp : Type where
  | mk (X infinity K S T C P N : BHist) : AlexandrovCompactificationUp
  deriving DecidableEq

def alexandrovCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alexandrovCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alexandrovCompactificationEncodeBHist h

def alexandrovCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alexandrovCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alexandrovCompactificationDecodeBHist tail)

private theorem AlexandrovCompactificationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, alexandrovCompactificationDecodeBHist
      (alexandrovCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def alexandrovCompactificationFields : AlexandrovCompactificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlexandrovCompactificationUp.mk X infinity K S T C P N =>
      [X, infinity, K, S, T, C, P, N]

def alexandrovCompactificationToEventFlow : AlexandrovCompactificationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (alexandrovCompactificationFields x).map alexandrovCompactificationEncodeBHist

private def alexandrovCompactificationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => alexandrovCompactificationEventAtDefault index rest

def alexandrovCompactificationFromEventFlow
    (ef : EventFlow) : Option AlexandrovCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AlexandrovCompactificationUp.mk
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 0 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 1 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 2 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 3 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 4 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 5 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 6 ef))
      (alexandrovCompactificationDecodeBHist
        (alexandrovCompactificationEventAtDefault 7 ef)))

private theorem AlexandrovCompactificationTasteGate_single_carrier_alignment_round_trip
    (x : AlexandrovCompactificationUp) :
    alexandrovCompactificationFromEventFlow
        (alexandrovCompactificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X infinity K S T C P N =>
      change
        some
          (AlexandrovCompactificationUp.mk
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist X))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist infinity))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist K))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist S))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist T))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist C))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist P))
            (alexandrovCompactificationDecodeBHist
              (alexandrovCompactificationEncodeBHist N))) =
          some (AlexandrovCompactificationUp.mk X infinity K S T C P N)
      rw [AlexandrovCompactificationTasteGate_single_carrier_alignment_decode X,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode infinity,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode K,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode S,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode T,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode C,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode P,
        AlexandrovCompactificationTasteGate_single_carrier_alignment_decode N]

private theorem AlexandrovCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlexandrovCompactificationUp} :
    alexandrovCompactificationToEventFlow x =
        alexandrovCompactificationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      alexandrovCompactificationFromEventFlow (alexandrovCompactificationToEventFlow x) =
        alexandrovCompactificationFromEventFlow (alexandrovCompactificationToEventFlow y) :=
    congrArg alexandrovCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AlexandrovCompactificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AlexandrovCompactificationTasteGate_single_carrier_alignment_round_trip y)))

private theorem AlexandrovCompactificationTasteGate_single_carrier_alignment_fields :
    ∀ x y : AlexandrovCompactificationUp,
      alexandrovCompactificationFields x = alexandrovCompactificationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ infinity₁ K₁ S₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ infinity₂ K₂ S₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance alexandrovCompactificationBHistCarrier :
    BHistCarrier AlexandrovCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := alexandrovCompactificationToEventFlow
  fromEventFlow := alexandrovCompactificationFromEventFlow

instance alexandrovCompactificationChapterTasteGate :
    ChapterTasteGate AlexandrovCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change alexandrovCompactificationFromEventFlow
      (alexandrovCompactificationToEventFlow x) = some x
    exact AlexandrovCompactificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AlexandrovCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance alexandrovCompactificationFieldFaithful :
    FieldFaithful AlexandrovCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := alexandrovCompactificationFields
  field_faithful := AlexandrovCompactificationTasteGate_single_carrier_alignment_fields

instance alexandrovCompactificationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial AlexandrovCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AlexandrovCompactificationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AlexandrovCompactificationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AlexandrovCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  alexandrovCompactificationChapterTasteGate

theorem AlexandrovCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist, alexandrovCompactificationDecodeBHist
      (alexandrovCompactificationEncodeBHist h) = h) ∧
      (alexandrovCompactificationEncodeBHist BHist.Empty = ([] : List BMark)) ∧
        ChapterTasteGate AlexandrovCompactificationUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨AlexandrovCompactificationTasteGate_single_carrier_alignment_decode, rfl,
      alexandrovCompactificationChapterTasteGate⟩

end BEDC.Derived.AlexandrovCompactificationUp
