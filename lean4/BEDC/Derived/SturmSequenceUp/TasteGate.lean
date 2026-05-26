import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SturmSequenceUp : Type where
  | mk (P D Q E V B W R H C K N : BHist) : SturmSequenceUp
  deriving DecidableEq

def sturmSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sturmSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sturmSequenceEncodeBHist h

def sturmSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sturmSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sturmSequenceDecodeBHist tail)

private theorem SturmSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sturmSequenceDecodeBHist (sturmSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sturmSequenceFields : SturmSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SturmSequenceUp.mk P D Q E V B W R H C K N => [P, D, Q, E, V, B, W, R, H, C, K, N]

def sturmSequenceToEventFlow : SturmSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sturmSequenceFields x).map sturmSequenceEncodeBHist

private def sturmSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sturmSequenceEventAt index rest

def sturmSequenceDecodeFields (ef : EventFlow) : SturmSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SturmSequenceUp.mk
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 0 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 1 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 2 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 3 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 4 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 5 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 6 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 7 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 8 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 9 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 10 ef))
    (sturmSequenceDecodeBHist (sturmSequenceEventAt 11 ef))

def sturmSequenceFromEventFlow (ef : EventFlow) : Option SturmSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (sturmSequenceDecodeFields ef)

private theorem SturmSequenceTasteGate_single_carrier_alignment_round_trip
    (x : SturmSequenceUp) :
    sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P D Q E V B W R H C K N =>
      change
        some
          (SturmSequenceUp.mk
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist P))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist D))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist Q))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist E))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist V))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist B))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist W))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist R))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist H))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist C))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist K))
            (sturmSequenceDecodeBHist (sturmSequenceEncodeBHist N))) =
          some (SturmSequenceUp.mk P D Q E V B W R H C K N)
      rw [SturmSequenceTasteGate_single_carrier_alignment_decode_encode P,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode D,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode Q,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode E,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode V,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode B,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode W,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode R,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode H,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode C,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode K,
        SturmSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem SturmSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SturmSequenceUp} :
    sturmSequenceToEventFlow x = sturmSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) =
        sturmSequenceFromEventFlow (sturmSequenceToEventFlow y) :=
    congrArg sturmSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SturmSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SturmSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance sturmSequenceBHistCarrier : BHistCarrier SturmSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sturmSequenceToEventFlow
  fromEventFlow := sturmSequenceFromEventFlow

instance sturmSequenceChapterTasteGate : ChapterTasteGate SturmSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) = some x
    exact SturmSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SturmSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SturmSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sturmSequenceChapterTasteGate

theorem SturmSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, sturmSequenceDecodeBHist (sturmSequenceEncodeBHist h) = h) ∧
      (∀ x : SturmSequenceUp, sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) = some x) ∧
        (∀ x y : SturmSequenceUp,
          sturmSequenceToEventFlow x = sturmSequenceToEventFlow y → x = y) ∧
          sturmSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SturmSequenceTasteGate_single_carrier_alignment_decode_encode,
      SturmSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SturmSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SturmSequenceUp
