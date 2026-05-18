import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisNatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisNatUp : Type where
  | mk (zeroSpine bridge provenance name : BHist) : AxisNatUp
  deriving DecidableEq

def axisNatEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisNatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisNatEncodeBHist h

def axisNatDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisNatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisNatDecodeBHist tail)

private theorem axisNatDecode_encode_bhist :
    ∀ h : BHist, axisNatDecodeBHist (axisNatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisNatToEventFlow : AxisNatUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisNatUp.mk zeroSpine bridge provenance name =>
      [[BMark.b0],
        axisNatEncodeBHist zeroSpine,
        [BMark.b1, BMark.b0],
        axisNatEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b0],
        axisNatEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisNatEncodeBHist name]

def axisNatFromEventFlow : EventFlow → Option AxisNatUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | zeroSpine :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | bridge :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | provenance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (AxisNatUp.mk
                                          (axisNatDecodeBHist zeroSpine)
                                          (axisNatDecodeBHist bridge)
                                          (axisNatDecodeBHist provenance)
                                          (axisNatDecodeBHist name))
                                  | _ :: _ => none

private theorem axisNat_round_trip :
    ∀ x : AxisNatUp, axisNatFromEventFlow (axisNatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk zeroSpine bridge provenance name =>
      change
        some
          (AxisNatUp.mk
            (axisNatDecodeBHist (axisNatEncodeBHist zeroSpine))
            (axisNatDecodeBHist (axisNatEncodeBHist bridge))
            (axisNatDecodeBHist (axisNatEncodeBHist provenance))
            (axisNatDecodeBHist (axisNatEncodeBHist name))) =
          some (AxisNatUp.mk zeroSpine bridge provenance name)
      rw [axisNatDecode_encode_bhist zeroSpine, axisNatDecode_encode_bhist bridge,
        axisNatDecode_encode_bhist provenance, axisNatDecode_encode_bhist name]

private theorem axisNatToEventFlow_injective {x y : AxisNatUp} :
    axisNatToEventFlow x = axisNatToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisNatFromEventFlow (axisNatToEventFlow x) =
        axisNatFromEventFlow (axisNatToEventFlow y) :=
    congrArg axisNatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisNat_round_trip x).symm (Eq.trans hread (axisNat_round_trip y)))

instance axisNatBHistCarrier : BHistCarrier AxisNatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisNatToEventFlow
  fromEventFlow := axisNatFromEventFlow

instance axisNatChapterTasteGate : ChapterTasteGate AxisNatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisNatFromEventFlow (axisNatToEventFlow x) = some x
    exact axisNat_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisNatToEventFlow_injective heq)

instance axisNatFieldFaithful : FieldFaithful AxisNatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AxisNatUp.mk zeroSpine bridge provenance name =>
        [zeroSpine, bridge, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk zeroSpine₁ bridge₁ provenance₁ name₁ =>
        cases y with
        | mk zeroSpine₂ bridge₂ provenance₂ name₂ =>
            injection h with hZero rest₁
            injection rest₁ with hBridge rest₂
            injection rest₂ with hProvenance rest₃
            injection rest₃ with hName _
            cases hZero
            cases hBridge
            cases hProvenance
            cases hName
            rfl

instance axisNatNontrivial : Nontrivial AxisNatUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisNatUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisNatUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hZero _ _ _
        cases hZero⟩

theorem AxisNatTasteGate_single_carrier_alignment :
    (∀ h : BHist, axisNatDecodeBHist (axisNatEncodeBHist h) = h) ∧
      (∀ x : AxisNatUp, axisNatFromEventFlow (axisNatToEventFlow x) = some x) ∧
        (∀ x y : AxisNatUp, axisNatToEventFlow x = axisNatToEventFlow y → x = y) ∧
          axisNatEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axisNatDecode_encode_bhist
  · constructor
    · exact axisNat_round_trip
    · constructor
      · intro x y heq
        exact axisNatToEventFlow_injective heq
      · rfl

end BEDC.Derived.AxisNatUp
