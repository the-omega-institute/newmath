import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedBoundedRealSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedBoundedRealSequenceUp : Type where
  | mk (I L U D W R E H C P N : BHist) : LocatedBoundedRealSequenceUp
  deriving DecidableEq

def locatedBoundedRealSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedBoundedRealSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedBoundedRealSequenceEncodeBHist h

def locatedBoundedRealSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedBoundedRealSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedBoundedRealSequenceDecodeBHist tail)

private theorem LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedBoundedRealSequenceFields : LocatedBoundedRealSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedBoundedRealSequenceUp.mk I L U D W R E H C P N => [I, L, U, D, W, R, E, H, C, P, N]

def locatedBoundedRealSequenceToEventFlow : LocatedBoundedRealSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedBoundedRealSequenceFields x).map locatedBoundedRealSequenceEncodeBHist

private def locatedBoundedRealSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedBoundedRealSequenceEventAt index rest

def locatedBoundedRealSequenceFromEventFlow : EventFlow → Option LocatedBoundedRealSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedBoundedRealSequenceUp.mk
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 0 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 1 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 2 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 3 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 4 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 5 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 6 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 7 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 8 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 9 ef))
          (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEventAt 10 ef)))

private theorem LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedBoundedRealSequenceUp,
      locatedBoundedRealSequenceFromEventFlow (locatedBoundedRealSequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L U D W R E H C P N =>
      change
        some
          (LocatedBoundedRealSequenceUp.mk
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist I))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist L))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist U))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist D))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist W))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist R))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist E))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist H))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist C))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist P))
            (locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist N))) =
          some (LocatedBoundedRealSequenceUp.mk I L U D W R E H C P N)
      rw [LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode I,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode L,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode U,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode D,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode W,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode R,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode E,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode H,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode C,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode P,
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedBoundedRealSequenceUp} :
    locatedBoundedRealSequenceToEventFlow x = locatedBoundedRealSequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedBoundedRealSequenceFromEventFlow (locatedBoundedRealSequenceToEventFlow x) =
        locatedBoundedRealSequenceFromEventFlow (locatedBoundedRealSequenceToEventFlow y) :=
    congrArg locatedBoundedRealSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedBoundedRealSequenceUp,
      locatedBoundedRealSequenceFields x = locatedBoundedRealSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ L₁ U₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ L₂ U₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedBoundedRealSequenceBHistCarrier :
    BHistCarrier LocatedBoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedBoundedRealSequenceToEventFlow
  fromEventFlow := locatedBoundedRealSequenceFromEventFlow

instance locatedBoundedRealSequenceChapterTasteGate :
    ChapterTasteGate LocatedBoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedBoundedRealSequenceFromEventFlow
      (locatedBoundedRealSequenceToEventFlow x) = some x
    exact LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedBoundedRealSequenceFieldFaithful :
    FieldFaithful LocatedBoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedBoundedRealSequenceFields
  field_faithful := LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_fields

instance locatedBoundedRealSequenceNontrivial :
    Nontrivial LocatedBoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedBoundedRealSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedBoundedRealSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedBoundedRealSequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedBoundedRealSequenceUp) ∧
      Nonempty (FieldFaithful LocatedBoundedRealSequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedBoundedRealSequenceUp) ∧
          (∀ h : BHist,
            locatedBoundedRealSequenceDecodeBHist (locatedBoundedRealSequenceEncodeBHist h) =
              h) ∧
            (∀ x : LocatedBoundedRealSequenceUp,
              locatedBoundedRealSequenceFromEventFlow
                (locatedBoundedRealSequenceToEventFlow x) = some x) ∧
              (∀ x y : LocatedBoundedRealSequenceUp,
                locatedBoundedRealSequenceToEventFlow x =
                    locatedBoundedRealSequenceToEventFlow y →
                  x = y) ∧
                locatedBoundedRealSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedBoundedRealSequenceChapterTasteGate⟩,
      ⟨locatedBoundedRealSequenceFieldFaithful⟩,
      ⟨locatedBoundedRealSequenceNontrivial⟩,
      LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_decode_encode,
      LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedBoundedRealSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedBoundedRealSequenceUp.TasteGate
