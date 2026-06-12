import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalChoiceSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalChoiceSequenceUp : Type where
  | mk (I D S R E H C P N : BHist) : CompactIntervalChoiceSequenceUp

def compactIntervalChoiceSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalChoiceSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalChoiceSequenceEncodeBHist h

def compactIntervalChoiceSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalChoiceSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalChoiceSequenceDecodeBHist tail)

private theorem CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_some_mk_congr
    {I' D' S' R' E' H' C' P' N' I D S R E H C P N : BHist}
    (hI : I' = I) (hD : D' = D) (hS : S' = S) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    some (CompactIntervalChoiceSequenceUp.mk I' D' S' R' E' H' C' P' N') =
      some (CompactIntervalChoiceSequenceUp.mk I D S R E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hD
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def compactIntervalChoiceSequenceFields :
    CompactIntervalChoiceSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalChoiceSequenceUp.mk I D S R E H C P N =>
      [I, D, S, R, E, H, C, P, N]

def compactIntervalChoiceSequenceToEventFlow :
    CompactIntervalChoiceSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactIntervalChoiceSequenceFields x).map
    compactIntervalChoiceSequenceEncodeBHist

private def compactIntervalChoiceSequenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactIntervalChoiceSequenceEventAtDefault index rest

def compactIntervalChoiceSequenceFromEventFlow
    (ef : EventFlow) : Option CompactIntervalChoiceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactIntervalChoiceSequenceUp.mk
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 0 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 1 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 2 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 3 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 4 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 5 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 6 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 7 ef))
      (compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEventAtDefault 8 ef)))

private theorem CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalChoiceSequenceUp,
      compactIntervalChoiceSequenceFromEventFlow
        (compactIntervalChoiceSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S R E H C P N =>
      exact
        CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_some_mk_congr
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode I)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode D)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode S)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode R)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode E)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode H)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode C)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode P)
          (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode N)

private theorem CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_injective
    {x y : CompactIntervalChoiceSequenceUp} :
    compactIntervalChoiceSequenceToEventFlow x =
      compactIntervalChoiceSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalChoiceSequenceFromEventFlow
          (compactIntervalChoiceSequenceToEventFlow x) =
        compactIntervalChoiceSequenceFromEventFlow
          (compactIntervalChoiceSequenceToEventFlow y) :=
    congrArg compactIntervalChoiceSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalChoiceSequenceBHistCarrier :
    BHistCarrier CompactIntervalChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalChoiceSequenceToEventFlow
  fromEventFlow := compactIntervalChoiceSequenceFromEventFlow

instance compactIntervalChoiceSequenceChapterTasteGate :
    ChapterTasteGate CompactIntervalChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalChoiceSequenceFromEventFlow
        (compactIntervalChoiceSequenceToEventFlow x) = some x
    exact CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_injective heq)

theorem CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactIntervalChoiceSequenceDecodeBHist
        (compactIntervalChoiceSequenceEncodeBHist h) = h) ∧
      (∀ x : CompactIntervalChoiceSequenceUp,
        compactIntervalChoiceSequenceFromEventFlow
          (compactIntervalChoiceSequenceToEventFlow x) = some x) ∧
      (∀ x y : CompactIntervalChoiceSequenceUp,
        compactIntervalChoiceSequenceToEventFlow x =
          compactIntervalChoiceSequenceToEventFlow y → x = y) ∧
      compactIntervalChoiceSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CompactIntervalChoiceSequenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CompactIntervalChoiceSequenceUp
