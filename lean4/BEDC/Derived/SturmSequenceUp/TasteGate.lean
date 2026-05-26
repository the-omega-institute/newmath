import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmSequenceUp.TasteGate

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

private theorem SturmSequenceTasteGate_single_carrier_alignment_decode :
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

def sturmSequenceToEventFlow : SturmSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sturmSequenceFields x).map sturmSequenceEncodeBHist

private def SturmSequenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SturmSequenceTasteGate_single_carrier_alignment_eventAt index rest

def sturmSequenceFromEventFlow (ef : EventFlow) : Option SturmSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SturmSequenceUp.mk
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 9 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 10 ef))
      (sturmSequenceDecodeBHist (SturmSequenceTasteGate_single_carrier_alignment_eventAt 11 ef)))

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
      rw [SturmSequenceTasteGate_single_carrier_alignment_decode P,
        SturmSequenceTasteGate_single_carrier_alignment_decode D,
        SturmSequenceTasteGate_single_carrier_alignment_decode Q,
        SturmSequenceTasteGate_single_carrier_alignment_decode E,
        SturmSequenceTasteGate_single_carrier_alignment_decode V,
        SturmSequenceTasteGate_single_carrier_alignment_decode B,
        SturmSequenceTasteGate_single_carrier_alignment_decode W,
        SturmSequenceTasteGate_single_carrier_alignment_decode R,
        SturmSequenceTasteGate_single_carrier_alignment_decode H,
        SturmSequenceTasteGate_single_carrier_alignment_decode C,
        SturmSequenceTasteGate_single_carrier_alignment_decode K,
        SturmSequenceTasteGate_single_carrier_alignment_decode N]

private theorem SturmSequenceTasteGate_single_carrier_alignment_injective
    {x y : SturmSequenceUp} :
    sturmSequenceToEventFlow x = sturmSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) =
        sturmSequenceFromEventFlow (sturmSequenceToEventFlow y) :=
    congrArg sturmSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SturmSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SturmSequenceTasteGate_single_carrier_alignment_round_trip y)))

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
    exact hxy (SturmSequenceTasteGate_single_carrier_alignment_injective heq)

theorem SturmSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, sturmSequenceDecodeBHist (sturmSequenceEncodeBHist h) = h) ∧
      (∀ x : SturmSequenceUp,
        sturmSequenceFromEventFlow (sturmSequenceToEventFlow x) = some x) ∧
        (∀ x y : SturmSequenceUp,
          sturmSequenceToEventFlow x = sturmSequenceToEventFlow y → x = y) ∧
          sturmSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SturmSequenceTasteGate_single_carrier_alignment_decode,
      SturmSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SturmSequenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.SturmSequenceUp.TasteGate
