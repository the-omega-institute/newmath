import BEDC.Derived.ValidatedNumericsUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ValidatedNumericsUp : Type where
  | mk :
      (interval tolerance modulus readback realSeal containment proofRow provenance
        nameCert : BHist) →
        ValidatedNumericsUp

def validatedNumericsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: validatedNumericsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: validatedNumericsEncodeBHist h

def validatedNumericsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (validatedNumericsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (validatedNumericsDecodeBHist tail)

private theorem validatedNumerics_decode_encode :
    ∀ h : BHist, validatedNumericsDecodeBHist (validatedNumericsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def validatedNumericsFields : ValidatedNumericsUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | ValidatedNumericsUp.mk interval tolerance modulus readback realSeal containment proofRow
      provenance nameCert =>
      [interval, tolerance, modulus, readback, realSeal, containment, proofRow, provenance,
        nameCert]

def validatedNumericsToEventFlow : ValidatedNumericsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (validatedNumericsFields x).map validatedNumericsEncodeBHist

def validatedNumericsFromEventFlow : EventFlow → Option ValidatedNumericsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | interval :: rest1 =>
        match rest1 with
        | tolerance :: rest2 =>
            match rest2 with
            | modulus :: rest3 =>
                match rest3 with
                | readback :: rest4 =>
                    match rest4 with
                    | realSeal :: rest5 =>
                        match rest5 with
                        | containment :: rest6 =>
                            match rest6 with
                            | proofRow :: rest7 =>
                                match rest7 with
                                | provenance :: rest8 =>
                                    match rest8 with
                                    | nameCert :: rest9 =>
                                        match rest9 with
                                        | [] =>
                                            some
                                              (ValidatedNumericsUp.mk
                                                (validatedNumericsDecodeBHist interval)
                                                (validatedNumericsDecodeBHist tolerance)
                                                (validatedNumericsDecodeBHist modulus)
                                                (validatedNumericsDecodeBHist readback)
                                                (validatedNumericsDecodeBHist realSeal)
                                                (validatedNumericsDecodeBHist containment)
                                                (validatedNumericsDecodeBHist proofRow)
                                                (validatedNumericsDecodeBHist provenance)
                                                (validatedNumericsDecodeBHist nameCert))
                                        | _ :: _ => none
                                    | [] => none
                                | [] => none
                            | [] => none
                        | [] => none
                    | [] => none
                | [] => none
            | [] => none
        | [] => none
    | [] => none

private theorem validatedNumerics_round_trip :
    ∀ x : ValidatedNumericsUp,
      validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk interval tolerance modulus readback realSeal containment proofRow provenance nameCert =>
      change
        some
            (ValidatedNumericsUp.mk
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist interval))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist tolerance))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist modulus))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist readback))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist realSeal))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist containment))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist proofRow))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist provenance))
              (validatedNumericsDecodeBHist (validatedNumericsEncodeBHist nameCert))) =
          some
            (ValidatedNumericsUp.mk interval tolerance modulus readback realSeal containment
              proofRow provenance nameCert)
      rw [validatedNumerics_decode_encode interval]
      rw [validatedNumerics_decode_encode tolerance]
      rw [validatedNumerics_decode_encode modulus]
      rw [validatedNumerics_decode_encode readback]
      rw [validatedNumerics_decode_encode realSeal]
      rw [validatedNumerics_decode_encode containment]
      rw [validatedNumerics_decode_encode proofRow]
      rw [validatedNumerics_decode_encode provenance]
      rw [validatedNumerics_decode_encode nameCert]

private theorem validatedNumericsToEventFlow_injective {x y : ValidatedNumericsUp} :
    validatedNumericsToEventFlow x = validatedNumericsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) :=
        (validatedNumerics_round_trip x).symm
      _ = validatedNumericsFromEventFlow (validatedNumericsToEventFlow y) :=
        congrArg validatedNumericsFromEventFlow hxy
      _ = some y := validatedNumerics_round_trip y
  exact Option.some.inj optionEq

instance validatedNumericsBHistCarrier : BHistCarrier ValidatedNumericsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := validatedNumericsToEventFlow
  fromEventFlow := validatedNumericsFromEventFlow

instance validatedNumericsChapterTasteGate : ChapterTasteGate ValidatedNumericsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) = some x
    exact validatedNumerics_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (validatedNumericsToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ValidatedNumericsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  validatedNumericsChapterTasteGate

theorem validatedNumericsTasteGate_single_carrier_alignment :
    (∀ x : ValidatedNumericsUp,
      validatedNumericsFromEventFlow (validatedNumericsToEventFlow x) = some x) ∧
    (∀ {x y : ValidatedNumericsUp},
      validatedNumericsToEventFlow x = validatedNumericsToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact validatedNumerics_round_trip
  · intro x y hxy
    exact validatedNumericsToEventFlow_injective hxy

end BEDC.Derived.ValidatedNumericsUp
