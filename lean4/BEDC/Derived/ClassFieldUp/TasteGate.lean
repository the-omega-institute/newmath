import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClassFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClassFieldUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (base adele extension classifier ledger : BHist) -> ClassFieldUp
  deriving DecidableEq

def ClassFieldTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ClassFieldTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ClassFieldTasteGate_single_carrier_alignment_encodeBHist h

def ClassFieldTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ClassFieldTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ClassFieldTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ClassFieldTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ClassFieldTasteGate_single_carrier_alignment_decodeBHist
        (ClassFieldTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ClassFieldTasteGate_single_carrier_alignment_fields : ClassFieldUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClassFieldUp.mk base adele extension classifier ledger =>
      [base, adele, extension, classifier, ledger]

def ClassFieldTasteGate_single_carrier_alignment_toEventFlow : ClassFieldUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ClassFieldTasteGate_single_carrier_alignment_fields x).map
        ClassFieldTasteGate_single_carrier_alignment_encodeBHist

def ClassFieldTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option ClassFieldUp
  -- BEDC touchpoint anchor: BHist BMark
  | [base, adele, extension, classifier, ledger] =>
      some
        (ClassFieldUp.mk
          (ClassFieldTasteGate_single_carrier_alignment_decodeBHist base)
          (ClassFieldTasteGate_single_carrier_alignment_decodeBHist adele)
          (ClassFieldTasteGate_single_carrier_alignment_decodeBHist extension)
          (ClassFieldTasteGate_single_carrier_alignment_decodeBHist classifier)
          (ClassFieldTasteGate_single_carrier_alignment_decodeBHist ledger))
  | _ => none

private theorem ClassFieldTasteGate_single_carrier_alignment_round_trip
    (x : ClassFieldUp) :
    ClassFieldTasteGate_single_carrier_alignment_fromEventFlow
      (ClassFieldTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk base adele extension classifier ledger =>
      change
        some
          (ClassFieldUp.mk
            (ClassFieldTasteGate_single_carrier_alignment_decodeBHist
              (ClassFieldTasteGate_single_carrier_alignment_encodeBHist base))
            (ClassFieldTasteGate_single_carrier_alignment_decodeBHist
              (ClassFieldTasteGate_single_carrier_alignment_encodeBHist adele))
            (ClassFieldTasteGate_single_carrier_alignment_decodeBHist
              (ClassFieldTasteGate_single_carrier_alignment_encodeBHist extension))
            (ClassFieldTasteGate_single_carrier_alignment_decodeBHist
              (ClassFieldTasteGate_single_carrier_alignment_encodeBHist classifier))
            (ClassFieldTasteGate_single_carrier_alignment_decodeBHist
              (ClassFieldTasteGate_single_carrier_alignment_encodeBHist ledger))) =
          some (ClassFieldUp.mk base adele extension classifier ledger)
      rw [ClassFieldTasteGate_single_carrier_alignment_decode_encode base,
        ClassFieldTasteGate_single_carrier_alignment_decode_encode adele,
        ClassFieldTasteGate_single_carrier_alignment_decode_encode extension,
        ClassFieldTasteGate_single_carrier_alignment_decode_encode classifier,
        ClassFieldTasteGate_single_carrier_alignment_decode_encode ledger]

private theorem ClassFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClassFieldUp} :
    ClassFieldTasteGate_single_carrier_alignment_toEventFlow x =
        ClassFieldTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ClassFieldTasteGate_single_carrier_alignment_fromEventFlow
          (ClassFieldTasteGate_single_carrier_alignment_toEventFlow x) =
        ClassFieldTasteGate_single_carrier_alignment_fromEventFlow
          (ClassFieldTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ClassFieldTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClassFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClassFieldTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClassFieldTasteGate_single_carrier_alignment_fields_faithful
    (x y : ClassFieldUp) :
    ClassFieldTasteGate_single_carrier_alignment_fields x =
        ClassFieldTasteGate_single_carrier_alignment_fields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk base₁ adele₁ extension₁ classifier₁ ledger₁ =>
      cases y with
      | mk base₂ adele₂ extension₂ classifier₂ ledger₂ =>
          injection h with hBase hRest₁
          injection hRest₁ with hAdele hRest₂
          injection hRest₂ with hExtension hRest₃
          injection hRest₃ with hClassifier hRest₄
          injection hRest₄ with hLedger _
          subst hBase
          subst hAdele
          subst hExtension
          subst hClassifier
          subst hLedger
          rfl

instance classFieldBHistCarrier : BHistCarrier ClassFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ClassFieldTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ClassFieldTasteGate_single_carrier_alignment_fromEventFlow

instance classFieldChapterTasteGate : ChapterTasteGate ClassFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ClassFieldTasteGate_single_carrier_alignment_fromEventFlow
        (ClassFieldTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ClassFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClassFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance classFieldFieldFaithful : FieldFaithful ClassFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ClassFieldTasteGate_single_carrier_alignment_fields
  field_faithful := ClassFieldTasteGate_single_carrier_alignment_fields_faithful

instance classFieldNontrivial : Nontrivial ClassFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClassFieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClassFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClassFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  classFieldChapterTasteGate

theorem ClassFieldTasteGate_single_carrier_alignment :
    (∀ base adele extension classifier ledger : BHist,
      ClassFieldTasteGate_single_carrier_alignment_fields
        (ClassFieldUp.mk base adele extension classifier ledger) =
          [base, adele, extension, classifier, ledger]) ∧
      ClassFieldTasteGate_single_carrier_alignment_encodeBHist (BHist.e0 BHist.Empty) =
        [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro base adele extension classifier ledger
    rfl
  · rfl

end BEDC.Derived.ClassFieldUp
