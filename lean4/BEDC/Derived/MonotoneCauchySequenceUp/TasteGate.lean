import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneCauchySequenceUp : Type where
  | mk (S W R D O T A H C P N : BHist) : MonotoneCauchySequenceUp
  deriving DecidableEq

def monotoneCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneCauchySequenceEncodeBHist h

def monotoneCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneCauchySequenceDecodeBHist tail)

private theorem monotoneCauchySequenceDecode_encode_bhist :
    ∀ h : BHist,
      monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneCauchySequenceFields : MonotoneCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneCauchySequenceUp.mk S W R D O T A H C P N => [S, W, R, D, O, T, A, H, C, P, N]

def monotoneCauchySequenceToEventFlow : MonotoneCauchySequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneCauchySequenceFields x).map monotoneCauchySequenceEncodeBHist

private def monotoneCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneCauchySequenceEventAt index rest

def monotoneCauchySequenceFromEventFlow
    (ef : EventFlow) : Option MonotoneCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneCauchySequenceUp.mk
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 0 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 1 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 2 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 3 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 4 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 5 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 6 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 7 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 8 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 9 ef))
      (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEventAt 10 ef)))

private theorem monotoneCauchySequence_round_trip
    (x : MonotoneCauchySequenceUp) :
    monotoneCauchySequenceFromEventFlow (monotoneCauchySequenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W R D O T A H C P N =>
      change
        some
          (MonotoneCauchySequenceUp.mk
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist S))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist W))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist R))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist D))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist O))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist T))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist A))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist H))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist C))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist P))
            (monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist N))) =
          some (MonotoneCauchySequenceUp.mk S W R D O T A H C P N)
      rw [monotoneCauchySequenceDecode_encode_bhist S,
        monotoneCauchySequenceDecode_encode_bhist W,
        monotoneCauchySequenceDecode_encode_bhist R,
        monotoneCauchySequenceDecode_encode_bhist D,
        monotoneCauchySequenceDecode_encode_bhist O,
        monotoneCauchySequenceDecode_encode_bhist T,
        monotoneCauchySequenceDecode_encode_bhist A,
        monotoneCauchySequenceDecode_encode_bhist H,
        monotoneCauchySequenceDecode_encode_bhist C,
        monotoneCauchySequenceDecode_encode_bhist P,
        monotoneCauchySequenceDecode_encode_bhist N]

private theorem monotoneCauchySequenceToEventFlow_injective
    {x y : MonotoneCauchySequenceUp} :
    monotoneCauchySequenceToEventFlow x =
        monotoneCauchySequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneCauchySequenceFromEventFlow (monotoneCauchySequenceToEventFlow x) =
        monotoneCauchySequenceFromEventFlow (monotoneCauchySequenceToEventFlow y) :=
    congrArg monotoneCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneCauchySequence_round_trip x).symm
      (Eq.trans hread (monotoneCauchySequence_round_trip y)))

private theorem monotoneCauchySequence_field_faithful :
    ∀ x y : MonotoneCauchySequenceUp,
      monotoneCauchySequenceFields x = monotoneCauchySequenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 R1 D1 O1 T1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 R2 D2 O2 T2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance monotoneCauchySequenceBHistCarrier :
    BHistCarrier MonotoneCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneCauchySequenceToEventFlow
  fromEventFlow := monotoneCauchySequenceFromEventFlow

instance monotoneCauchySequenceChapterTasteGate :
    ChapterTasteGate MonotoneCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneCauchySequenceFromEventFlow (monotoneCauchySequenceToEventFlow x) =
        some x
    exact monotoneCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneCauchySequenceToEventFlow_injective heq)

instance monotoneCauchySequenceFieldFaithful :
    FieldFaithful MonotoneCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneCauchySequenceFields
  field_faithful := monotoneCauchySequence_field_faithful

instance monotoneCauchySequenceNontrivial : Nontrivial MonotoneCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonotoneCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MonotoneCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonotoneCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneCauchySequenceChapterTasteGate

theorem MonotoneCauchySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, monotoneCauchySequenceDecodeBHist (monotoneCauchySequenceEncodeBHist h) = h) ∧
      (∀ x : MonotoneCauchySequenceUp,
        monotoneCauchySequenceFromEventFlow (monotoneCauchySequenceToEventFlow x) = some x) ∧
        (∀ x y : MonotoneCauchySequenceUp,
          monotoneCauchySequenceToEventFlow x = monotoneCauchySequenceToEventFlow y → x = y) ∧
          monotoneCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow BHistCarrier ChapterTasteGate
  exact
    ⟨monotoneCauchySequenceDecode_encode_bhist,
      monotoneCauchySequence_round_trip,
      (fun _ _ heq => monotoneCauchySequenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MonotoneCauchySequenceUp
