import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNameUp : Type where
  | mk (source radius modulus tail selector sealRow name : BHist) : RegularCauchyNameUp
  deriving DecidableEq

def regularCauchyNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNameEncodeBHist h

def regularCauchyNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNameDecodeBHist tail)

private theorem regularCauchyName_decode_encode :
    ∀ h : BHist, regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyNameFields : RegularCauchyNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNameUp.mk source radius modulus tail selector sealRow name =>
      [source, radius, modulus, tail, selector, sealRow, name]

def regularCauchyNameToEventFlow : RegularCauchyNameUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyNameFields x).map regularCauchyNameEncodeBHist

def regularCauchyNameFromEventFlow : EventFlow → Option RegularCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | source :: rest1 =>
        match rest1 with
        | [] => none
        | radius :: rest2 =>
            match rest2 with
            | [] => none
            | modulus :: rest3 =>
                match rest3 with
                | [] => none
                | tail :: rest4 =>
                    match rest4 with
                    | [] => none
                    | selector :: rest5 =>
                        match rest5 with
                        | [] => none
                        | sealRow :: rest6 =>
                            match rest6 with
                            | [] => none
                            | name :: rest7 =>
                                match rest7 with
                                | [] =>
                                    some
                                      (RegularCauchyNameUp.mk
                                        (regularCauchyNameDecodeBHist source)
                                        (regularCauchyNameDecodeBHist radius)
                                        (regularCauchyNameDecodeBHist modulus)
                                        (regularCauchyNameDecodeBHist tail)
                                        (regularCauchyNameDecodeBHist selector)
                                        (regularCauchyNameDecodeBHist sealRow)
                                        (regularCauchyNameDecodeBHist name))
                                | _ :: _ => none

private theorem regularCauchyName_round_trip :
    ∀ x : RegularCauchyNameUp,
      regularCauchyNameFromEventFlow (regularCauchyNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source radius modulus tail selector sealRow name =>
      change
        some
            (RegularCauchyNameUp.mk
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist source))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist radius))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist modulus))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist tail))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist selector))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist sealRow))
              (regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist name))) =
          some
            (RegularCauchyNameUp.mk source radius modulus tail selector sealRow name)
      rw [regularCauchyName_decode_encode source, regularCauchyName_decode_encode radius,
        regularCauchyName_decode_encode modulus, regularCauchyName_decode_encode tail,
        regularCauchyName_decode_encode selector, regularCauchyName_decode_encode sealRow,
        regularCauchyName_decode_encode name]

private theorem regularCauchyNameToEventFlow_injective {x y : RegularCauchyNameUp} :
    regularCauchyNameToEventFlow x = regularCauchyNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNameFromEventFlow (regularCauchyNameToEventFlow x) =
        regularCauchyNameFromEventFlow (regularCauchyNameToEventFlow y) :=
    congrArg regularCauchyNameFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (regularCauchyName_round_trip x).symm
        (Eq.trans hread (regularCauchyName_round_trip y)))

private theorem regularCauchyName_fields_faithful :
    ∀ x y : RegularCauchyNameUp,
      regularCauchyNameFields x = regularCauchyNameFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source radius modulus tail selector sealRow name =>
      cases y with
      | mk source' radius' modulus' tail' selector' sealRow' name' =>
          cases hfields
          rfl

instance regularCauchyNameBHistCarrier : BHistCarrier RegularCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNameToEventFlow
  fromEventFlow := regularCauchyNameFromEventFlow

instance regularCauchyNameChapterTasteGate : ChapterTasteGate RegularCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNameFromEventFlow (regularCauchyNameToEventFlow x) = some x
    exact regularCauchyName_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNameToEventFlow_injective heq)

instance regularCauchyNameFieldFaithful : FieldFaithful RegularCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyNameFields
  field_faithful := regularCauchyName_fields_faithful

instance regularCauchyNameNontrivial : Nontrivial RegularCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyNameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyNameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyNameChapterTasteGate

theorem RegularCauchyNameTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyNameDecodeBHist (regularCauchyNameEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyNameUp,
        regularCauchyNameFromEventFlow (regularCauchyNameToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyNameUp,
          regularCauchyNameToEventFlow x = regularCauchyNameToEventFlow y → x = y) ∧
          regularCauchyNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact regularCauchyName_decode_encode
  · constructor
    · exact regularCauchyName_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyNameToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyNameUp
