import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MoscoRecoverySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MoscoRecoverySequenceUp : Type where
  | mk (X F W A G Q E M H C P N : BHist) : MoscoRecoverySequenceUp
  deriving DecidableEq

def moscoRecoverySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: moscoRecoverySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: moscoRecoverySequenceEncodeBHist h

def moscoRecoverySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (moscoRecoverySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (moscoRecoverySequenceDecodeBHist tail)

private theorem MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def moscoRecoverySequenceFields : MoscoRecoverySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MoscoRecoverySequenceUp.mk X F W A G Q E M H C P N => [X, F, W, A, G, Q, E, M, H, C, P, N]

def moscoRecoverySequenceToEventFlow : MoscoRecoverySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (moscoRecoverySequenceFields x).map moscoRecoverySequenceEncodeBHist

private def moscoRecoverySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => moscoRecoverySequenceEventAt index rest

def moscoRecoverySequenceFromEventFlow : EventFlow → Option MoscoRecoverySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (MoscoRecoverySequenceUp.mk
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 0 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 1 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 2 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 3 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 4 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 5 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 6 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 7 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 8 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 9 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 10 flow))
        (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEventAt 11 flow)))

private theorem MoscoRecoverySequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MoscoRecoverySequenceUp,
      moscoRecoverySequenceFromEventFlow (moscoRecoverySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F W A G Q E M H C P N =>
      change
        some
          (MoscoRecoverySequenceUp.mk
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist X))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist F))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist W))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist A))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist G))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist Q))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist E))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist M))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist H))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist C))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist P))
            (moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist N))) =
          some (MoscoRecoverySequenceUp.mk X F W A G Q E M H C P N)
      rw [MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode X,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode F,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode W,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode A,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode G,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode Q,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode E,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode M,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode H,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode C,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode P,
        MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem MoscoRecoverySequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MoscoRecoverySequenceUp} :
    moscoRecoverySequenceToEventFlow x = moscoRecoverySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      moscoRecoverySequenceFromEventFlow (moscoRecoverySequenceToEventFlow x) =
        moscoRecoverySequenceFromEventFlow (moscoRecoverySequenceToEventFlow y) :=
    congrArg moscoRecoverySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MoscoRecoverySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MoscoRecoverySequenceTasteGate_single_carrier_alignment_round_trip y)))

instance moscoRecoverySequenceBHistCarrier : BHistCarrier MoscoRecoverySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := moscoRecoverySequenceToEventFlow
  fromEventFlow := moscoRecoverySequenceFromEventFlow

instance moscoRecoverySequenceChapterTasteGate : ChapterTasteGate MoscoRecoverySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change moscoRecoverySequenceFromEventFlow (moscoRecoverySequenceToEventFlow x) = some x
    exact MoscoRecoverySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MoscoRecoverySequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MoscoRecoverySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  moscoRecoverySequenceChapterTasteGate

theorem MoscoRecoverySequenceTasteGate_single_carrier_alignment :
    moscoRecoverySequenceEncodeBHist BHist.Empty = [] ∧
      moscoRecoverySequenceEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ h : BHist, moscoRecoverySequenceDecodeBHist (moscoRecoverySequenceEncodeBHist h) = h) ∧
          (∀ x : MoscoRecoverySequenceUp,
            moscoRecoverySequenceFromEventFlow (moscoRecoverySequenceToEventFlow x) = some x) ∧
            Nonempty (BHistCarrier MoscoRecoverySequenceUp) ∧
              Nonempty (ChapterTasteGate MoscoRecoverySequenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl,
      MoscoRecoverySequenceTasteGate_single_carrier_alignment_decode_encode,
      MoscoRecoverySequenceTasteGate_single_carrier_alignment_round_trip,
      ⟨moscoRecoverySequenceBHistCarrier⟩,
      ⟨moscoRecoverySequenceChapterTasteGate⟩⟩

end BEDC.Derived.MoscoRecoverySequenceUp
