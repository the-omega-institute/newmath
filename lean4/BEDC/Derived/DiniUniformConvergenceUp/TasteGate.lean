import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniUniformConvergenceUp : Type where
  | mk
      (compactMetricData totalBoundedNets continuousFamily monotoneWindow streamWindows
        regSeqReadback realSeals transportRows continuationRows provenance nameCert : BHist) :
      DiniUniformConvergenceUp
  deriving DecidableEq

def diniUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniUniformConvergenceEncodeBHist h

def diniUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniUniformConvergenceDecodeBHist tail)

private theorem DiniUniformConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      diniUniformConvergenceDecodeBHist (diniUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diniUniformConvergenceFields : DiniUniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniUniformConvergenceUp.mk compactMetricData totalBoundedNets continuousFamily
      monotoneWindow streamWindows regSeqReadback realSeals transportRows continuationRows
      provenance nameCert =>
      [compactMetricData, totalBoundedNets, continuousFamily, monotoneWindow, streamWindows,
        regSeqReadback, realSeals, transportRows, continuationRows, provenance, nameCert]

def diniUniformConvergenceToEventFlow : DiniUniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diniUniformConvergenceFields x).map diniUniformConvergenceEncodeBHist

private def diniUniformConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diniUniformConvergenceEventAtDefault index rest

def diniUniformConvergenceFromEventFlow : EventFlow → Option DiniUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DiniUniformConvergenceUp.mk
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 0 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 1 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 2 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 3 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 4 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 5 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 6 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 7 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 8 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 9 ef))
        (diniUniformConvergenceDecodeBHist (diniUniformConvergenceEventAtDefault 10 ef)))

private theorem DiniUniformConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiniUniformConvergenceUp,
      diniUniformConvergenceFromEventFlow (diniUniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetricData totalBoundedNets continuousFamily monotoneWindow streamWindows
      regSeqReadback realSeals transportRows continuationRows provenance nameCert =>
      change
        some
          (DiniUniformConvergenceUp.mk
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist compactMetricData))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist totalBoundedNets))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist continuousFamily))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist monotoneWindow))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist streamWindows))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist regSeqReadback))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist realSeals))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist transportRows))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist continuationRows))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist provenance))
            (diniUniformConvergenceDecodeBHist
              (diniUniformConvergenceEncodeBHist nameCert))) =
          some
            (DiniUniformConvergenceUp.mk compactMetricData totalBoundedNets continuousFamily
              monotoneWindow streamWindows regSeqReadback realSeals transportRows
              continuationRows provenance nameCert)
      rw [DiniUniformConvergenceTasteGate_single_carrier_alignment_decode compactMetricData,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode totalBoundedNets,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode continuousFamily,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode monotoneWindow,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode streamWindows,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode regSeqReadback,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode realSeals,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode transportRows,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode continuationRows,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode provenance,
        DiniUniformConvergenceTasteGate_single_carrier_alignment_decode nameCert]

private theorem diniUniformConvergenceToEventFlow_injective
    {x y : DiniUniformConvergenceUp} :
    diniUniformConvergenceToEventFlow x = diniUniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniUniformConvergenceFromEventFlow (diniUniformConvergenceToEventFlow x) =
        diniUniformConvergenceFromEventFlow (diniUniformConvergenceToEventFlow y) :=
    congrArg diniUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniUniformConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiniUniformConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem diniUniformConvergence_field_faithful :
    ∀ x y : DiniUniformConvergenceUp,
      diniUniformConvergenceFields x = diniUniformConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk compactMetricData₁ totalBoundedNets₁ continuousFamily₁ monotoneWindow₁ streamWindows₁
      regSeqReadback₁ realSeals₁ transportRows₁ continuationRows₁ provenance₁ nameCert₁ =>
      cases y with
      | mk compactMetricData₂ totalBoundedNets₂ continuousFamily₂ monotoneWindow₂
          streamWindows₂ regSeqReadback₂ realSeals₂ transportRows₂ continuationRows₂
          provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance diniUniformConvergenceBHistCarrier : BHistCarrier DiniUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniUniformConvergenceToEventFlow
  fromEventFlow := diniUniformConvergenceFromEventFlow

instance diniUniformConvergenceChapterTasteGate :
    ChapterTasteGate DiniUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diniUniformConvergenceFromEventFlow (diniUniformConvergenceToEventFlow x) = some x
    exact DiniUniformConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diniUniformConvergenceToEventFlow_injective heq)

instance diniUniformConvergenceFieldFaithful : FieldFaithful DiniUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diniUniformConvergenceFields
  field_faithful := diniUniformConvergence_field_faithful

def taste_gate : ChapterTasteGate DiniUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diniUniformConvergenceChapterTasteGate

theorem DiniUniformConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DiniUniformConvergenceUp) ∧
      Nonempty (ChapterTasteGate DiniUniformConvergenceUp) ∧
      Nonempty (FieldFaithful DiniUniformConvergenceUp) ∧
      (∀ h : BHist,
        diniUniformConvergenceDecodeBHist (diniUniformConvergenceEncodeBHist h) = h) ∧
      (∀ x : DiniUniformConvergenceUp,
        diniUniformConvergenceFromEventFlow (diniUniformConvergenceToEventFlow x) = some x) ∧
      (∀ x y : DiniUniformConvergenceUp,
        diniUniformConvergenceToEventFlow x = diniUniformConvergenceToEventFlow y → x = y) ∧
      diniUniformConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨diniUniformConvergenceBHistCarrier⟩
  constructor
  · exact ⟨diniUniformConvergenceChapterTasteGate⟩
  constructor
  · exact ⟨diniUniformConvergenceFieldFaithful⟩
  constructor
  · exact DiniUniformConvergenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact DiniUniformConvergenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact diniUniformConvergenceToEventFlow_injective heq
  · rfl

end BEDC.Derived.DiniUniformConvergenceUp
