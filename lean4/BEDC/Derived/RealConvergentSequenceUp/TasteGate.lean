import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealConvergentSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealConvergentSequenceUp : Type where
  | mk (S L D M W R H K P N : BHist) : RealConvergentSequenceUp
  deriving DecidableEq

def realConvergentSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realConvergentSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realConvergentSequenceEncodeBHist h

def realConvergentSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realConvergentSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realConvergentSequenceDecodeBHist tail)

private theorem realConvergentSequence_decode_encode :
    ∀ h : BHist, realConvergentSequenceDecodeBHist
      (realConvergentSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realConvergentSequenceFields : RealConvergentSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealConvergentSequenceUp.mk S L D M W R H K P N => [S, L, D, M, W, R, H, K, P, N]

def realConvergentSequenceToEventFlow : RealConvergentSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realConvergentSequenceEncodeBHist (realConvergentSequenceFields x)

private def realConvergentSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realConvergentSequenceEventAtDefault index rest

def realConvergentSequenceFromEventFlow : EventFlow → Option RealConvergentSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealConvergentSequenceUp.mk
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 0 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 1 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 2 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 3 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 4 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 5 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 6 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 7 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 8 ef))
        (realConvergentSequenceDecodeBHist (realConvergentSequenceEventAtDefault 9 ef)))

private theorem realConvergentSequence_round_trip :
    ∀ x : RealConvergentSequenceUp,
      realConvergentSequenceFromEventFlow (realConvergentSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L D M W R H K P N =>
      change
        some
          (RealConvergentSequenceUp.mk
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist S))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist L))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist D))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist M))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist W))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist R))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist H))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist K))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist P))
            (realConvergentSequenceDecodeBHist (realConvergentSequenceEncodeBHist N))) =
          some (RealConvergentSequenceUp.mk S L D M W R H K P N)
      rw [realConvergentSequence_decode_encode S,
        realConvergentSequence_decode_encode L,
        realConvergentSequence_decode_encode D,
        realConvergentSequence_decode_encode M,
        realConvergentSequence_decode_encode W,
        realConvergentSequence_decode_encode R,
        realConvergentSequence_decode_encode H,
        realConvergentSequence_decode_encode K,
        realConvergentSequence_decode_encode P,
        realConvergentSequence_decode_encode N]

private theorem realConvergentSequenceToEventFlow_injective {x y : RealConvergentSequenceUp} :
    realConvergentSequenceToEventFlow x = realConvergentSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realConvergentSequenceFromEventFlow (realConvergentSequenceToEventFlow x) =
        realConvergentSequenceFromEventFlow (realConvergentSequenceToEventFlow y) :=
    congrArg realConvergentSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realConvergentSequence_round_trip x).symm
      (Eq.trans hread (realConvergentSequence_round_trip y)))

private theorem realConvergentSequence_field_faithful :
    ∀ x y : RealConvergentSequenceUp,
      realConvergentSequenceFields x = realConvergentSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 L1 D1 M1 W1 R1 H1 K1 P1 N1 =>
      cases y with
      | mk S2 L2 D2 M2 W2 R2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance realConvergentSequenceBHistCarrier : BHistCarrier RealConvergentSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realConvergentSequenceToEventFlow
  fromEventFlow := realConvergentSequenceFromEventFlow

instance realConvergentSequenceChapterTasteGate :
    ChapterTasteGate RealConvergentSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realConvergentSequenceFromEventFlow
      (realConvergentSequenceToEventFlow x) = some x
    exact realConvergentSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realConvergentSequenceToEventFlow_injective heq)

instance realConvergentSequenceFieldFaithful :
    FieldFaithful RealConvergentSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realConvergentSequenceFields
  field_faithful := realConvergentSequence_field_faithful

instance realConvergentSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealConvergentSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealConvergentSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealConvergentSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealConvergentSequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealConvergentSequenceUp) ∧
      Nonempty (ChapterTasteGate RealConvergentSequenceUp) ∧
        Nonempty (FieldFaithful RealConvergentSequenceUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial RealConvergentSequenceUp) ∧
            realConvergentSequenceEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              realConvergentSequenceEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro realConvergentSequenceBHistCarrier,
      Nonempty.intro realConvergentSequenceChapterTasteGate,
      Nonempty.intro realConvergentSequenceFieldFaithful,
      Nonempty.intro realConvergentSequenceNontrivial,
      rfl,
      rfl⟩

end BEDC.Derived.RealConvergentSequenceUp
