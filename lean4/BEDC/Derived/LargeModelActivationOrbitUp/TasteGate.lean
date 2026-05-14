import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelActivationOrbitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelActivationOrbitUp : Type where
  | mk :
      (modelWeight transition activationWindow prompt output auditRefusal transport route
        provenance nameCert : BHist) →
        LargeModelActivationOrbitUp
  deriving DecidableEq

def largeModelActivationOrbitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelActivationOrbitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelActivationOrbitEncodeBHist h

def largeModelActivationOrbitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelActivationOrbitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelActivationOrbitDecodeBHist tail)

private theorem largeModelActivationOrbitDecode_encode_bhist :
    ∀ h : BHist,
      largeModelActivationOrbitDecodeBHist (largeModelActivationOrbitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def largeModelActivationOrbitToEventFlow : LargeModelActivationOrbitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelActivationOrbitUp.mk modelWeight transition activationWindow prompt output
      auditRefusal transport route provenance nameCert =>
      [largeModelActivationOrbitEncodeBHist modelWeight,
        largeModelActivationOrbitEncodeBHist transition,
        largeModelActivationOrbitEncodeBHist activationWindow,
        largeModelActivationOrbitEncodeBHist prompt,
        largeModelActivationOrbitEncodeBHist output,
        largeModelActivationOrbitEncodeBHist auditRefusal,
        largeModelActivationOrbitEncodeBHist transport,
        largeModelActivationOrbitEncodeBHist route,
        largeModelActivationOrbitEncodeBHist provenance,
        largeModelActivationOrbitEncodeBHist nameCert]

def largeModelActivationOrbitFromEventFlow : EventFlow → Option LargeModelActivationOrbitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | modelWeight :: rest1 =>
      match rest1 with
      | [] => none
      | transition :: rest2 =>
          match rest2 with
          | [] => none
          | activationWindow :: rest3 =>
              match rest3 with
              | [] => none
              | prompt :: rest4 =>
                  match rest4 with
                  | [] => none
                  | output :: rest5 =>
                      match rest5 with
                      | [] => none
                      | auditRefusal :: rest6 =>
                          match rest6 with
                          | [] => none
                          | transport :: rest7 =>
                              match rest7 with
                              | [] => none
                              | route :: rest8 =>
                                  match rest8 with
                                  | [] => none
                                  | provenance :: rest9 =>
                                      match rest9 with
                                      | [] => none
                                      | nameCert :: rest10 =>
                                          match rest10 with
                                          | [] =>
                                              some
                                                (LargeModelActivationOrbitUp.mk
                                                  (largeModelActivationOrbitDecodeBHist
                                                    modelWeight)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    transition)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    activationWindow)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    prompt)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    output)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    auditRefusal)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    transport)
                                                  (largeModelActivationOrbitDecodeBHist route)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    provenance)
                                                  (largeModelActivationOrbitDecodeBHist
                                                    nameCert))
                                          | _ :: _ => none

private theorem largeModelActivationOrbit_round_trip :
    ∀ x : LargeModelActivationOrbitUp,
      largeModelActivationOrbitFromEventFlow (largeModelActivationOrbitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modelWeight transition activationWindow prompt output auditRefusal transport route
      provenance nameCert =>
      change
        some
          (LargeModelActivationOrbitUp.mk
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist modelWeight))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist transition))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist activationWindow))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist prompt))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist output))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist auditRefusal))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist transport))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist route))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist provenance))
            (largeModelActivationOrbitDecodeBHist
              (largeModelActivationOrbitEncodeBHist nameCert))) =
          some
            (LargeModelActivationOrbitUp.mk modelWeight transition activationWindow prompt
              output auditRefusal transport route provenance nameCert)
      rw [largeModelActivationOrbitDecode_encode_bhist modelWeight,
        largeModelActivationOrbitDecode_encode_bhist transition,
        largeModelActivationOrbitDecode_encode_bhist activationWindow,
        largeModelActivationOrbitDecode_encode_bhist prompt,
        largeModelActivationOrbitDecode_encode_bhist output,
        largeModelActivationOrbitDecode_encode_bhist auditRefusal,
        largeModelActivationOrbitDecode_encode_bhist transport,
        largeModelActivationOrbitDecode_encode_bhist route,
        largeModelActivationOrbitDecode_encode_bhist provenance,
        largeModelActivationOrbitDecode_encode_bhist nameCert]

private theorem largeModelActivationOrbitToEventFlow_injective
    {x y : LargeModelActivationOrbitUp} :
    largeModelActivationOrbitToEventFlow x =
      largeModelActivationOrbitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelActivationOrbitFromEventFlow (largeModelActivationOrbitToEventFlow x) =
        largeModelActivationOrbitFromEventFlow (largeModelActivationOrbitToEventFlow y) :=
    congrArg largeModelActivationOrbitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelActivationOrbit_round_trip x).symm
      (Eq.trans hread (largeModelActivationOrbit_round_trip y)))

instance largeModelActivationOrbitBHistCarrier :
    BHistCarrier LargeModelActivationOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelActivationOrbitToEventFlow
  fromEventFlow := largeModelActivationOrbitFromEventFlow

instance largeModelActivationOrbitChapterTasteGate :
    ChapterTasteGate LargeModelActivationOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      largeModelActivationOrbitFromEventFlow (largeModelActivationOrbitToEventFlow x) =
        some x
    exact largeModelActivationOrbit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelActivationOrbitToEventFlow_injective heq)

instance largeModelActivationOrbitFieldFaithful :
    FieldFaithful LargeModelActivationOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelActivationOrbitUp.mk modelWeight transition activationWindow prompt output
        auditRefusal transport route provenance nameCert =>
        [modelWeight, transition, activationWindow, prompt, output, auditRefusal, transport,
          route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk modelWeight₁ transition₁ activationWindow₁ prompt₁ output₁ auditRefusal₁
        transport₁ route₁ provenance₁ nameCert₁ =>
        cases y with
        | mk modelWeight₂ transition₂ activationWindow₂ prompt₂ output₂ auditRefusal₂
            transport₂ route₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance largeModelActivationOrbitNontrivial :
    Nontrivial LargeModelActivationOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelActivationOrbitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelActivationOrbitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LargeModelActivationOrbitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      largeModelActivationOrbitDecodeBHist (largeModelActivationOrbitEncodeBHist h) = h) ∧
      (∀ x : LargeModelActivationOrbitUp,
        largeModelActivationOrbitFromEventFlow (largeModelActivationOrbitToEventFlow x) =
          some x) ∧
        (∀ x y : LargeModelActivationOrbitUp,
          largeModelActivationOrbitToEventFlow x =
            largeModelActivationOrbitToEventFlow y → x = y) ∧
          largeModelActivationOrbitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelActivationOrbitDecode_encode_bhist
  · constructor
    · exact largeModelActivationOrbit_round_trip
    · constructor
      · intro x y heq
        exact largeModelActivationOrbitToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelActivationOrbitUp
