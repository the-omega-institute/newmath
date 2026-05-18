import BEDC.Derived.AxisNatUp.TasteGate
import BEDC.Derived.AxisZeckendorf.AxisAdd
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
  | mk (left right result ledger nameCert : BHist) : AxisAddUp
  deriving DecidableEq

def axisAddUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisAddUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisAddUpEncodeBHist h

def axisAddUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisAddUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisAddUpDecodeBHist tail)

private theorem axisAddUpDecode_encode_bhist :
    ∀ h : BHist, axisAddUpDecodeBHist (axisAddUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisAddUpToEventFlow : AxisAddUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisAddUp.mk left right result ledger nameCert =>
      [[BMark.b0],
        axisAddUpEncodeBHist left,
        [BMark.b1, BMark.b0],
        axisAddUpEncodeBHist right,
        [BMark.b1, BMark.b1, BMark.b0],
        axisAddUpEncodeBHist result,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisAddUpEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisAddUpEncodeBHist nameCert]

def axisAddUpFromEventFlow : EventFlow → Option AxisAddUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | left :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | right :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | result :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AxisAddUp.mk
                                                  (axisAddUpDecodeBHist left)
                                                  (axisAddUpDecodeBHist right)
                                                  (axisAddUpDecodeBHist result)
                                                  (axisAddUpDecodeBHist ledger)
                                                  (axisAddUpDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem axisAddUp_round_trip :
    ∀ x : AxisAddUp, axisAddUpFromEventFlow (axisAddUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right result ledger nameCert =>
      change
        some
          (AxisAddUp.mk
            (axisAddUpDecodeBHist (axisAddUpEncodeBHist left))
            (axisAddUpDecodeBHist (axisAddUpEncodeBHist right))
            (axisAddUpDecodeBHist (axisAddUpEncodeBHist result))
            (axisAddUpDecodeBHist (axisAddUpEncodeBHist ledger))
            (axisAddUpDecodeBHist (axisAddUpEncodeBHist nameCert))) =
          some (AxisAddUp.mk left right result ledger nameCert)
      rw [axisAddUpDecode_encode_bhist left, axisAddUpDecode_encode_bhist right,
        axisAddUpDecode_encode_bhist result, axisAddUpDecode_encode_bhist ledger,
        axisAddUpDecode_encode_bhist nameCert]

private theorem axisAddUpToEventFlow_injective {x y : AxisAddUp} :
    axisAddUpToEventFlow x = axisAddUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisAddUpFromEventFlow (axisAddUpToEventFlow x) =
        axisAddUpFromEventFlow (axisAddUpToEventFlow y) :=
    congrArg axisAddUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisAddUp_round_trip x).symm (Eq.trans hread (axisAddUp_round_trip y)))

instance axisAddUpBHistCarrier : BHistCarrier AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisAddUpToEventFlow
  fromEventFlow := axisAddUpFromEventFlow

instance axisAddUpChapterTasteGate : ChapterTasteGate AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisAddUpFromEventFlow (axisAddUpToEventFlow x) = some x
    exact axisAddUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisAddUpToEventFlow_injective heq)

instance axisAddUpFieldFaithful : FieldFaithful AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AxisAddUp.mk left right result ledger nameCert =>
        [left, right, result, ledger, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk left₁ right₁ result₁ ledger₁ nameCert₁ =>
        cases y with
        | mk left₂ right₂ result₂ ledger₂ nameCert₂ =>
            injection h with hLeft rest₁
            injection rest₁ with hRight rest₂
            injection rest₂ with hResult rest₃
            injection rest₃ with hLedger rest₄
            injection rest₄ with hNameCert _
            cases hLeft
            cases hRight
            cases hResult
            cases hLedger
            cases hNameCert
            rfl

instance axisAddUpNontrivial : Nontrivial AxisAddUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisAddUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisAddUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hLeft _ _ _ _
        cases hLeft⟩

theorem AxisAddUp_single_carrier_alignment :
    (∀ h : BHist, axisAddUpDecodeBHist (axisAddUpEncodeBHist h) = h) ∧
      (∀ x : AxisAddUp, axisAddUpFromEventFlow (axisAddUpToEventFlow x) = some x) ∧
        (∀ x y : AxisAddUp, axisAddUpToEventFlow x = axisAddUpToEventFlow y → x = y) ∧
          (∀ h k r : BHist,
            AxisAddPatternSpec h k r → ZeroSpine h ∧ ZeroSpine k ∧ Cont h k r) := by
  -- BEDC touchpoint anchor: BHist BMark ZeroSpine Cont
  constructor
  · exact axisAddUpDecode_encode_bhist
  · constructor
    · exact axisAddUp_round_trip
    · constructor
      · intro x y heq
        exact axisAddUpToEventFlow_injective heq
      · intro h k r pattern
        exact pattern

end BEDC.Derived.AxisAddUp
