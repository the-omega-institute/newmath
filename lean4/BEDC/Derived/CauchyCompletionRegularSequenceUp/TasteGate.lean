import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionRegularSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionRegularSequenceUp : Type where
  | mk (R E M U S H C P N : BHist) : CauchyCompletionRegularSequenceUp
  deriving DecidableEq

def cauchyCompletionRegularSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionRegularSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionRegularSequenceEncodeBHist h

def cauchyCompletionRegularSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionRegularSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionRegularSequenceDecodeBHist tail)

private theorem CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionRegularSequenceFields :
    CauchyCompletionRegularSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionRegularSequenceUp.mk R E M U S H C P N =>
      [R, E, M, U, S, H, C, P, N]

def cauchyCompletionRegularSequenceToEventFlow :
    CauchyCompletionRegularSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionRegularSequenceFields x).map
        cauchyCompletionRegularSequenceEncodeBHist

private def cauchyCompletionRegularSequenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionRegularSequenceEventAtDefault index rest

def cauchyCompletionRegularSequenceFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionRegularSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionRegularSequenceUp.mk
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 0 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 1 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 2 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 3 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 4 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 5 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 6 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 7 ef))
      (cauchyCompletionRegularSequenceDecodeBHist
        (cauchyCompletionRegularSequenceEventAtDefault 8 ef)))

private theorem CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionRegularSequenceUp) :
    cauchyCompletionRegularSequenceFromEventFlow
      (cauchyCompletionRegularSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R E M U S H C P N =>
      change
        some
          (CauchyCompletionRegularSequenceUp.mk
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist R))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist E))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist M))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist U))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist S))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist H))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist C))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist P))
            (cauchyCompletionRegularSequenceDecodeBHist
              (cauchyCompletionRegularSequenceEncodeBHist N))) =
          some (CauchyCompletionRegularSequenceUp.mk R E M U S H C P N)
      rw [CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode M,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_injective
    {x y : CauchyCompletionRegularSequenceUp} :
    cauchyCompletionRegularSequenceToEventFlow x =
      cauchyCompletionRegularSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionRegularSequenceFromEventFlow
          (cauchyCompletionRegularSequenceToEventFlow x) =
        cauchyCompletionRegularSequenceFromEventFlow
          (cauchyCompletionRegularSequenceToEventFlow y) :=
    congrArg cauchyCompletionRegularSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionRegularSequenceBHistCarrier :
    BHistCarrier CauchyCompletionRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionRegularSequenceToEventFlow
  fromEventFlow := cauchyCompletionRegularSequenceFromEventFlow

instance cauchyCompletionRegularSequenceChapterTasteGate :
    ChapterTasteGate CauchyCompletionRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionRegularSequenceFromEventFlow
        (cauchyCompletionRegularSequenceToEventFlow x) = some x
    exact CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_injective heq)

theorem CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier CauchyCompletionRegularSequenceUp,
      Nonempty (@ChapterTasteGate CauchyCompletionRegularSequenceUp carrier)) ∧
      (∀ h : BHist,
        cauchyCompletionRegularSequenceDecodeBHist
          (cauchyCompletionRegularSequenceEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionRegularSequenceUp,
        cauchyCompletionRegularSequenceFromEventFlow
          (cauchyCompletionRegularSequenceToEventFlow x) = some x) ∧
      cauchyCompletionRegularSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyCompletionRegularSequenceBHistCarrier,
        ⟨cauchyCompletionRegularSequenceChapterTasteGate⟩⟩,
      CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_decode,
      CauchyCompletionRegularSequenceTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionRegularSequenceUp
