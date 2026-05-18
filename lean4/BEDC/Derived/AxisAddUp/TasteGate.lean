import BEDC.Derived.AxisZeckendorf.AxisAdd
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisAddUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived.AxisZeckendorf.Spine
open BEDC.Derived.AxisZeckendorf.AxisAdd

inductive AxisAddUp : Type where
  | mk : (source pattern classifier stability ledger : BHist) → AxisAddUp
  deriving DecidableEq

def axisAddEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisAddEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisAddEncodeBHist h

def axisAddDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisAddDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisAddDecodeBHist tail)

private theorem AxisAddTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, axisAddDecodeBHist (axisAddEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def axisAddFields : AxisAddUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxisAddUp.mk source pattern classifier stability ledger =>
      [source, pattern, classifier, stability, ledger]

def axisAddToEventFlow : AxisAddUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (axisAddFields x).map axisAddEncodeBHist

def axisAddFromEventFlow : EventFlow → Option AxisAddUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | pattern :: rest1 =>
          match rest1 with
          | [] => none
          | classifier :: rest2 =>
              match rest2 with
              | [] => none
              | stability :: rest3 =>
                  match rest3 with
                  | [] => none
                  | ledger :: rest4 =>
                      match rest4 with
                      | [] =>
                          some
                            (AxisAddUp.mk
                              (axisAddDecodeBHist source)
                              (axisAddDecodeBHist pattern)
                              (axisAddDecodeBHist classifier)
                              (axisAddDecodeBHist stability)
                              (axisAddDecodeBHist ledger))
                      | _ :: _ => none

private theorem AxisAddTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AxisAddUp, axisAddFromEventFlow (axisAddToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger =>
      change
        some
          (AxisAddUp.mk
            (axisAddDecodeBHist (axisAddEncodeBHist source))
            (axisAddDecodeBHist (axisAddEncodeBHist pattern))
            (axisAddDecodeBHist (axisAddEncodeBHist classifier))
            (axisAddDecodeBHist (axisAddEncodeBHist stability))
            (axisAddDecodeBHist (axisAddEncodeBHist ledger))) =
          some (AxisAddUp.mk source pattern classifier stability ledger)
      rw [AxisAddTasteGate_single_carrier_alignment_decode source,
        AxisAddTasteGate_single_carrier_alignment_decode pattern,
        AxisAddTasteGate_single_carrier_alignment_decode classifier,
        AxisAddTasteGate_single_carrier_alignment_decode stability,
        AxisAddTasteGate_single_carrier_alignment_decode ledger]

private theorem axisAddToEventFlow_injective {x y : AxisAddUp} :
    axisAddToEventFlow x = axisAddToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisAddFromEventFlow (axisAddToEventFlow x) =
        axisAddFromEventFlow (axisAddToEventFlow y) :=
    congrArg axisAddFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AxisAddTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AxisAddTasteGate_single_carrier_alignment_round_trip y)))

private theorem AxisAddTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AxisAddUp, axisAddFields x = axisAddFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ pattern₁ classifier₁ stability₁ ledger₁ =>
      cases y with
      | mk source₂ pattern₂ classifier₂ stability₂ ledger₂ =>
          injection hfields with hSource tail0
          injection tail0 with hPattern tail1
          injection tail1 with hClassifier tail2
          injection tail2 with hStability tail3
          injection tail3 with hLedger _
          subst hSource
          subst hPattern
          subst hClassifier
          subst hStability
          subst hLedger
          rfl

instance axisAddBHistCarrier : BHistCarrier AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisAddToEventFlow
  fromEventFlow := axisAddFromEventFlow

instance axisAddChapterTasteGate : ChapterTasteGate AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisAddFromEventFlow (axisAddToEventFlow x) = some x
    exact AxisAddTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisAddToEventFlow_injective heq)

instance axisAddFieldFaithful : FieldFaithful AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axisAddFields
  field_faithful := AxisAddTasteGate_single_carrier_alignment_fields_faithful

instance axisAddNontrivial : Nontrivial AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisAddUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisAddUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisAddUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisAddChapterTasteGate

theorem AxisAddTasteGate_single_carrier_alignment :
    (∀ h : BHist, axisAddDecodeBHist (axisAddEncodeBHist h) = h) ∧
      (∀ x : AxisAddUp, axisAddFromEventFlow (axisAddToEventFlow x) = some x) ∧
        (∀ x y : AxisAddUp, axisAddToEventFlow x = axisAddToEventFlow y → x = y) ∧
          axisAddEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AxisAddTasteGate_single_carrier_alignment_decode,
      AxisAddTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => axisAddToEventFlow_injective heq),
      rfl⟩

theorem AxisAddUp_single_carrier_alignment :
    (∀ h : BHist, axisAddDecodeBHist (axisAddEncodeBHist h) = h) ∧
      (∀ x : AxisAddUp, axisAddFromEventFlow (axisAddToEventFlow x) = some x) ∧
        (∀ x y : AxisAddUp, axisAddToEventFlow x = axisAddToEventFlow y → x = y) ∧
          (∀ h k r : BHist,
            AxisAddPatternSpec h k r → ZeroSpine h ∧ ZeroSpine k ∧ Cont h k r) := by
  -- BEDC touchpoint anchor: BHist BMark ZeroSpine Cont
  exact
    ⟨AxisAddTasteGate_single_carrier_alignment_decode,
      AxisAddTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => axisAddToEventFlow_injective heq),
      fun _ _ _ pattern => pattern⟩

end BEDC.Derived.AxisAddUp
