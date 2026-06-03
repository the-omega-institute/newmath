import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformlyCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformlyCauchySequenceUp : Type where
  | mk (S T W D R E H C P N : BHist) : UniformlyCauchySequenceUp
  deriving DecidableEq

def uniformlyCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformlyCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformlyCauchySequenceEncodeBHist h

def uniformlyCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformlyCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformlyCauchySequenceDecodeBHist tail)

private theorem UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformlyCauchySequenceDecodeBHist
      (uniformlyCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformlyCauchySequenceFields : UniformlyCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformlyCauchySequenceUp.mk S T W D R E H C P N => [S, T, W, D, R, E, H, C, P, N]

def uniformlyCauchySequenceToEventFlow : UniformlyCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformlyCauchySequenceFields x).map uniformlyCauchySequenceEncodeBHist

private def uniformlyCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformlyCauchySequenceEventAt index rest

def uniformlyCauchySequenceFromEventFlow : EventFlow → Option UniformlyCauchySequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (UniformlyCauchySequenceUp.mk
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 0 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 1 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 2 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 3 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 4 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 5 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 6 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 7 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 8 ef))
          (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEventAt 9 ef)))

private theorem UniformlyCauchySequenceTasteGate_single_carrier_alignment_round_trip
    (x : UniformlyCauchySequenceUp) :
    uniformlyCauchySequenceFromEventFlow
      (uniformlyCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T W D R E H C P N =>
      change
        some
            (UniformlyCauchySequenceUp.mk
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist S))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist T))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist W))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist D))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist R))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist E))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist H))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist C))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist P))
              (uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist N))) =
          some (UniformlyCauchySequenceUp.mk S T W D R E H C P N)
      rw [UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode S,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode T,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode W,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode D,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode R,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode E,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode H,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode C,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode P,
        UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformlyCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformlyCauchySequenceUp} :
    uniformlyCauchySequenceToEventFlow x = uniformlyCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformlyCauchySequenceFromEventFlow (uniformlyCauchySequenceToEventFlow x) =
        uniformlyCauchySequenceFromEventFlow (uniformlyCauchySequenceToEventFlow y) :=
    congrArg uniformlyCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformlyCauchySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformlyCauchySequenceTasteGate_single_carrier_alignment_round_trip y)))

instance uniformlyCauchySequenceBHistCarrier : BHistCarrier UniformlyCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformlyCauchySequenceToEventFlow
  fromEventFlow := uniformlyCauchySequenceFromEventFlow

instance uniformlyCauchySequenceChapterTasteGate :
    ChapterTasteGate UniformlyCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformlyCauchySequenceFromEventFlow
        (uniformlyCauchySequenceToEventFlow x) = some x
    exact UniformlyCauchySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformlyCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformlyCauchySequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformlyCauchySequenceDecodeBHist (uniformlyCauchySequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformlyCauchySequenceUp) ∧
        Nonempty (ChapterTasteGate UniformlyCauchySequenceUp) ∧
          uniformlyCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformlyCauchySequenceTasteGate_single_carrier_alignment_decode_encode,
      ⟨uniformlyCauchySequenceBHistCarrier⟩,
      ⟨uniformlyCauchySequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformlyCauchySequenceUp
