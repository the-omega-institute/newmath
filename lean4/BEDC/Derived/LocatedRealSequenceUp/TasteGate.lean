import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealSequenceUp : Type where
  | mk (S L M D R E H C P N : BHist) : LocatedRealSequenceUp
  deriving DecidableEq

def locatedRealSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealSequenceEncodeBHist h

def locatedRealSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealSequenceDecodeBHist tail)

private theorem LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealSequenceFields : LocatedRealSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealSequenceUp.mk S L M D R E H C P N => [S, L, M, D, R, E, H, C, P, N]

def locatedRealSequenceToEventFlow : LocatedRealSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealSequenceFields x).map locatedRealSequenceEncodeBHist

private def locatedRealSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealSequenceEventAt index rest

def locatedRealSequenceFromEventFlow (ef : EventFlow) :
    Option LocatedRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealSequenceUp.mk
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 0 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 1 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 2 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 3 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 4 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 5 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 6 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 7 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 8 ef))
      (locatedRealSequenceDecodeBHist (locatedRealSequenceEventAt 9 ef)))

private theorem LocatedRealSequenceTasteGate_single_carrier_alignment_round_trip
    (x : LocatedRealSequenceUp) :
    locatedRealSequenceFromEventFlow (locatedRealSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S L M D R E H C P N =>
      change
        some
          (LocatedRealSequenceUp.mk
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist S))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist L))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist M))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist D))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist R))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist E))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist H))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist C))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist P))
            (locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist N))) =
          some (LocatedRealSequenceUp.mk S L M D R E H C P N)
      rw [LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode S,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode L,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode M,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode D,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode R,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode E,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealSequenceUp} :
    locatedRealSequenceToEventFlow x = locatedRealSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealSequenceFromEventFlow (locatedRealSequenceToEventFlow x) =
        locatedRealSequenceFromEventFlow (locatedRealSequenceToEventFlow y) :=
    congrArg locatedRealSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedRealSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealSequenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedRealSequenceUp,
      locatedRealSequenceFields x = locatedRealSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ L₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ L₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedRealSequenceBHistCarrier : BHistCarrier LocatedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealSequenceToEventFlow
  fromEventFlow := locatedRealSequenceFromEventFlow

instance locatedRealSequenceChapterTasteGate :
    ChapterTasteGate LocatedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealSequenceFromEventFlow (locatedRealSequenceToEventFlow x) = some x
    exact LocatedRealSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealSequenceFieldFaithful :
    FieldFaithful LocatedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealSequenceFields
  field_faithful := LocatedRealSequenceTasteGate_single_carrier_alignment_fields_faithful

instance locatedRealSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealSequenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedRealSequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealSequenceChapterTasteGate

theorem LocatedRealSequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRealSequenceUp) ∧
      Nonempty (FieldFaithful LocatedRealSequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRealSequenceUp) ∧
          (∀ h : BHist,
            locatedRealSequenceDecodeBHist (locatedRealSequenceEncodeBHist h) = h) ∧
            (∀ x : LocatedRealSequenceUp,
              locatedRealSequenceFromEventFlow (locatedRealSequenceToEventFlow x) = some x) ∧
              (∀ x y : LocatedRealSequenceUp,
                locatedRealSequenceToEventFlow x = locatedRealSequenceToEventFlow y → x = y) ∧
                locatedRealSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨locatedRealSequenceChapterTasteGate⟩,
      ⟨locatedRealSequenceFieldFaithful⟩,
      ⟨locatedRealSequenceNontrivial⟩,
      LocatedRealSequenceTasteGate_single_carrier_alignment_decode_encode,
      LocatedRealSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealSequenceUp.TasteGate
