import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrueferSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrueferSequenceUp : Type where
  | mk (n V L S D E T H C G N : BHist) : PrueferSequenceUp
  deriving DecidableEq

def prueferSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: prueferSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: prueferSequenceEncodeBHist h

def prueferSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (prueferSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (prueferSequenceDecodeBHist tail)

private theorem prueferSequenceDecode_encode :
    ∀ h : BHist, prueferSequenceDecodeBHist (prueferSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def prueferSequenceFields : PrueferSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrueferSequenceUp.mk n V L S D E T H C G N => [n, V, L, S, D, E, T, H, C, G, N]

def prueferSequenceToEventFlow : PrueferSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (prueferSequenceFields x).map prueferSequenceEncodeBHist

private def prueferSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => prueferSequenceEventAt index rest

def prueferSequenceFromEventFlow (ef : EventFlow) : Option PrueferSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PrueferSequenceUp.mk
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 0 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 1 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 2 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 3 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 4 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 5 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 6 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 7 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 8 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 9 ef))
      (prueferSequenceDecodeBHist (prueferSequenceEventAt 10 ef)))

private theorem prueferSequence_round_trip (x : PrueferSequenceUp) :
    prueferSequenceFromEventFlow (prueferSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk n V L S D E T H C G N =>
      change
        some
          (PrueferSequenceUp.mk
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist n))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist V))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist L))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist S))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist D))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist E))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist T))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist H))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist C))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist G))
            (prueferSequenceDecodeBHist (prueferSequenceEncodeBHist N))) =
          some (PrueferSequenceUp.mk n V L S D E T H C G N)
      rw [prueferSequenceDecode_encode n, prueferSequenceDecode_encode V,
        prueferSequenceDecode_encode L, prueferSequenceDecode_encode S,
        prueferSequenceDecode_encode D, prueferSequenceDecode_encode E,
        prueferSequenceDecode_encode T, prueferSequenceDecode_encode H,
        prueferSequenceDecode_encode C, prueferSequenceDecode_encode G,
        prueferSequenceDecode_encode N]

private theorem prueferSequenceToEventFlow_injective {x y : PrueferSequenceUp} :
    prueferSequenceToEventFlow x = prueferSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      prueferSequenceFromEventFlow (prueferSequenceToEventFlow x) =
        prueferSequenceFromEventFlow (prueferSequenceToEventFlow y) :=
    congrArg prueferSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (prueferSequence_round_trip x).symm
      (Eq.trans hread (prueferSequence_round_trip y)))

instance prueferSequenceBHistCarrier : BHistCarrier PrueferSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := prueferSequenceToEventFlow
  fromEventFlow := prueferSequenceFromEventFlow

instance prueferSequenceChapterTasteGate : ChapterTasteGate PrueferSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change prueferSequenceFromEventFlow (prueferSequenceToEventFlow x) = some x
    exact prueferSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (prueferSequenceToEventFlow_injective heq)

def prueferSequenceTasteGate : ChapterTasteGate PrueferSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  prueferSequenceChapterTasteGate

theorem PrueferSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, prueferSequenceDecodeBHist (prueferSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PrueferSequenceUp) ∧
        Nonempty (ChapterTasteGate PrueferSequenceUp) ∧
          prueferSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact prueferSequenceDecode_encode
  · constructor
    · exact Nonempty.intro prueferSequenceBHistCarrier
    · constructor
      · exact Nonempty.intro prueferSequenceChapterTasteGate
      · rfl

end BEDC.Derived.PrueferSequenceUp
