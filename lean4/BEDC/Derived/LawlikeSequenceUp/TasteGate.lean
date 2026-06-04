import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawlikeSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawlikeSequenceUp : Type where
  | mk (R W O H C P N : BHist) : LawlikeSequenceUp
  deriving DecidableEq

def lawlikeSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlikeSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlikeSequenceEncodeBHist h

def lawlikeSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlikeSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlikeSequenceDecodeBHist tail)

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lawlikeSequenceFields : LawlikeSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N => [R, W, O, H, C, P, N]

def lawlikeSequenceToEventFlow : LawlikeSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lawlikeSequenceFields x).map lawlikeSequenceEncodeBHist

private def lawlikeSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lawlikeSequenceEventAtDefault index rest

def lawlikeSequenceFromEventFlow (ef : EventFlow) : Option LawlikeSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LawlikeSequenceUp.mk
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 0 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 1 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 2 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 3 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 4 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 5 ef))
      (lawlikeSequenceDecodeBHist (lawlikeSequenceEventAtDefault 6 ef)))

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LawlikeSequenceUp,
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R W O H C P N =>
      change
        some
          (LawlikeSequenceUp.mk
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist R))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist W))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist O))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist H))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist C))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist P))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist N))) =
          some (LawlikeSequenceUp.mk R W O H C P N)
      rw [LawlikeSequenceTasteGate_single_carrier_alignment_decode R,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode W,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode O,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode H,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode C,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode P,
        LawlikeSequenceTasteGate_single_carrier_alignment_decode N]

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LawlikeSequenceUp} :
    lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) =
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow y) :=
    congrArg lawlikeSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LawlikeSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LawlikeSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : LawlikeSequenceUp, lawlikeSequenceFields x = lawlikeSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lawlikeSequenceBHistCarrier : BHistCarrier LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlikeSequenceToEventFlow
  fromEventFlow := lawlikeSequenceFromEventFlow

instance lawlikeSequenceChapterTasteGate : ChapterTasteGate LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x
    exact LawlikeSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lawlikeSequenceFieldFaithful : FieldFaithful LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawlikeSequenceFields
  field_faithful := LawlikeSequenceTasteGate_single_carrier_alignment_fields

instance lawlikeSequenceNontrivial : Nontrivial LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawlikeSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LawlikeSequenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LawlikeSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlikeSequenceChapterTasteGate

theorem LawlikeSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h) ∧
      (∀ x : LawlikeSequenceUp,
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x) ∧
        (∀ x y : LawlikeSequenceUp,
          lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y) ∧
          lawlikeSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨LawlikeSequenceTasteGate_single_carrier_alignment_decode,
      LawlikeSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LawlikeSequenceUp
