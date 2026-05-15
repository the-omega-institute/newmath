import BEDC.Derived.EmptyUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyUp : Type where
  | zero : BHist → EmptyUp
  | one : BHist → EmptyUp

def emptyUpEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyUpEncodeBHist h

def emptyUpDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyUpDecodeBHist tail)

private theorem emptyUpDecode_encode_bhist :
    ∀ h : BHist, emptyUpDecodeBHist (emptyUpEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem emptyUp_zero_congr {h h' : BHist} (hh : h' = h) :
    EmptyUp.zero h' = EmptyUp.zero h := by
  cases hh
  rfl

private theorem emptyUp_one_congr {h h' : BHist} (hh : h' = h) :
    EmptyUp.one h' = EmptyUp.one h := by
  cases hh
  rfl

def emptyUpToEventFlow : EmptyUp → EventFlow
  | EmptyUp.zero h => [[BMark.b0], emptyUpEncodeBHist h]
  | EmptyUp.one h => [[BMark.b1], [BMark.b0], emptyUpEncodeBHist h]

def emptyUpFromEventFlow : EventFlow → Option EmptyUp
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | raw :: rest' =>
          match rest' with
          | [] => some (EmptyUp.zero (emptyUpDecodeBHist raw))
          | raw' :: rest'' =>
              match rest'' with
              | [] => some (EmptyUp.one (emptyUpDecodeBHist raw'))
              | _ :: _ => none

def emptyUpFields : EmptyUp → List BHist
  | EmptyUp.zero h => [BHist.e0 h]
  | EmptyUp.one h => [BHist.e1 h]

private theorem emptyUp_round_trip :
    ∀ x : EmptyUp, emptyUpFromEventFlow (emptyUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | zero h =>
      change some (EmptyUp.zero (emptyUpDecodeBHist (emptyUpEncodeBHist h))) =
        some (EmptyUp.zero h)
      exact congrArg some (emptyUp_zero_congr (emptyUpDecode_encode_bhist h))
  | one h =>
      change some (EmptyUp.one (emptyUpDecodeBHist (emptyUpEncodeBHist h))) =
        some (EmptyUp.one h)
      exact congrArg some (emptyUp_one_congr (emptyUpDecode_encode_bhist h))

private theorem emptyUpToEventFlow_injective :
    ∀ x y : EmptyUp, emptyUpToEventFlow x = emptyUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hxy
  have optionEq : some x = some y := by
    calc
      some x = emptyUpFromEventFlow (emptyUpToEventFlow x) := (emptyUp_round_trip x).symm
      _ = emptyUpFromEventFlow (emptyUpToEventFlow y) := congrArg emptyUpFromEventFlow hxy
      _ = some y := emptyUp_round_trip y
  exact Option.some.inj optionEq

instance emptyUpBHistCarrier : BHistCarrier EmptyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyUpToEventFlow
  fromEventFlow := emptyUpFromEventFlow

instance emptyUpChapterTasteGate : ChapterTasteGate EmptyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := emptyUp_round_trip
  layer_separation := by
    intro x y hneq hflow
    exact hneq (emptyUpToEventFlow_injective x y hflow)

def emptyUpTasteGate : ChapterTasteGate EmptyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyUpChapterTasteGate

instance emptyUpFieldFaithful : FieldFaithful EmptyUp where
  fields := emptyUpFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | zero a =>
        cases y with
        | zero b =>
            injection h with hab _
            cases hab
            rfl
        | one b =>
            injection h with htag _
            cases htag
    | one a =>
        cases y with
        | zero b =>
            injection h with htag _
            cases htag
        | one b =>
            injection h with hab _
            cases hab
            rfl

theorem EmptyUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, emptyUpDecodeBHist (emptyUpEncodeBHist h) = h) ∧
      (∀ x : EmptyUp, emptyUpFromEventFlow (emptyUpToEventFlow x) = some x) ∧
        (∀ x y : EmptyUp, emptyUpToEventFlow x = emptyUpToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate EmptyUp) ∧
            (∀ x y : EmptyUp, emptyUpFields x = emptyUpFields y → x = y) ∧
              (∀ x : EmptyUp, ∃ h : BHist, List.Mem h (emptyUpFields x)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact emptyUpDecode_encode_bhist
  · constructor
    · exact emptyUp_round_trip
    · constructor
      · intro x y hxy
        exact emptyUpToEventFlow_injective x y hxy
      · constructor
        · exact ⟨emptyUpTasteGate⟩
        · constructor
          · intro x y h
            cases x with
            | zero a =>
                cases y with
                | zero b =>
                    injection h with hab _
                    cases hab
                    rfl
                | one b =>
                    injection h with htag _
                    cases htag
            | one a =>
                cases y with
                | zero b =>
                    injection h with htag _
                    cases htag
                | one b =>
                    injection h with hab _
                    cases hab
                    rfl
          · intro x
            cases x with
            | zero h =>
                exact ⟨BHist.e0 h, List.Mem.head _⟩
            | one h =>
                exact ⟨BHist.e1 h, List.Mem.head _⟩

end BEDC.Derived.EmptyUp
