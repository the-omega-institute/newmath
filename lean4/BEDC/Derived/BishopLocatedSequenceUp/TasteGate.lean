import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedSequenceUp : Type where
  | mk (S L R E H C P N : BHist) : BishopLocatedSequenceUp
  deriving DecidableEq

def bishopLocatedSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedSequenceEncodeBHist h

def bishopLocatedSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedSequenceDecodeBHist tail)

private theorem BishopLocatedSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedSequenceDecodeBHist
        (bishopLocatedSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedSequenceFields :
    BishopLocatedSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedSequenceUp.mk S L R E H C P N => [S, L, R, E, H, C, P, N]

def bishopLocatedSequenceToEventFlow :
    BishopLocatedSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedSequenceFields x).map bishopLocatedSequenceEncodeBHist

private def bishopLocatedSequenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedSequenceEventAtDefault index rest

def bishopLocatedSequenceFromEventFlow
    (ef : EventFlow) : Option BishopLocatedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedSequenceUp.mk
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 0 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 1 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 2 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 3 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 4 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 5 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 6 ef))
      (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEventAtDefault 7 ef)))

private theorem BishopLocatedSequenceTasteGate_single_carrier_alignment_round_trip
    (x : BishopLocatedSequenceUp) :
    bishopLocatedSequenceFromEventFlow
      (bishopLocatedSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S L R E H C P N =>
      change
        some
          (BishopLocatedSequenceUp.mk
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist S))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist L))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist R))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist E))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist H))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist C))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist P))
            (bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist N))) =
          some (BishopLocatedSequenceUp.mk S L R E H C P N)
      rw [BishopLocatedSequenceTasteGate_single_carrier_alignment_decode S,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode L,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode R,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode E,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode H,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode C,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode P,
        BishopLocatedSequenceTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedSequenceTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedSequenceUp} :
    bishopLocatedSequenceToEventFlow x =
      bishopLocatedSequenceToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedSequenceFromEventFlow
          (bishopLocatedSequenceToEventFlow x) =
        bishopLocatedSequenceFromEventFlow
          (bishopLocatedSequenceToEventFlow y) :=
    congrArg bishopLocatedSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedSequenceBHistCarrier :
    BHistCarrier BishopLocatedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedSequenceToEventFlow
  fromEventFlow := bishopLocatedSequenceFromEventFlow

instance bishopLocatedSequenceChapterTasteGate :
    ChapterTasteGate BishopLocatedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedSequenceFromEventFlow
        (bishopLocatedSequenceToEventFlow x) = some x
    exact BishopLocatedSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedSequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BishopLocatedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedSequenceChapterTasteGate

theorem BishopLocatedSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedSequenceDecodeBHist (bishopLocatedSequenceEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedSequenceUp,
        bishopLocatedSequenceFromEventFlow (bishopLocatedSequenceToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedSequenceUp,
          bishopLocatedSequenceToEventFlow x = bishopLocatedSequenceToEventFlow y → x = y) ∧
          bishopLocatedSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopLocatedSequenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BishopLocatedSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BishopLocatedSequenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.BishopLocatedSequenceUp
