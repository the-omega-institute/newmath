import BEDC.Derived.RegularCauchyNetUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNetToken : Type where
  | mk :
      (directed tail window readback sealRow transport replay provenance localName : BHist) →
      RegularCauchyNetToken
  deriving DecidableEq

def regularCauchyNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNetEncodeBHist h

def regularCauchyNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNetDecodeBHist tail)

private theorem regularCauchyNet_decode_encode_bhist :
    ∀ h : BHist, regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyNetFields : RegularCauchyNetToken → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNetToken.mk directed tail window readback sealRow transport replay provenance
      localName =>
      [directed, tail, window, readback, sealRow, transport, replay, provenance, localName]

def regularCauchyNetToEventFlow : RegularCauchyNetToken → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyNetEncodeBHist (regularCauchyNetFields x)

def regularCauchyNetFromEventFlow : EventFlow → Option RegularCauchyNetToken
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | directed :: rest0 =>
      match rest0 with
      | [] => none
      | tail :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | sealRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RegularCauchyNetToken.mk
                                              (regularCauchyNetDecodeBHist directed)
                                              (regularCauchyNetDecodeBHist tail)
                                              (regularCauchyNetDecodeBHist window)
                                              (regularCauchyNetDecodeBHist readback)
                                              (regularCauchyNetDecodeBHist sealRow)
                                              (regularCauchyNetDecodeBHist transport)
                                              (regularCauchyNetDecodeBHist replay)
                                              (regularCauchyNetDecodeBHist provenance)
                                              (regularCauchyNetDecodeBHist localName))
                                      | _ :: _ => none

private theorem regularCauchyNet_round_trip :
    ∀ x : RegularCauchyNetToken,
      regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk directed tail window readback sealRow transport replay provenance localName =>
      change
        some
          (RegularCauchyNetToken.mk
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist directed))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist tail))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist window))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist readback))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist sealRow))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist transport))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist replay))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist provenance))
            (regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist localName))) =
          some
            (RegularCauchyNetToken.mk directed tail window readback sealRow transport replay
              provenance localName)
      rw [regularCauchyNet_decode_encode_bhist directed,
        regularCauchyNet_decode_encode_bhist tail,
        regularCauchyNet_decode_encode_bhist window,
        regularCauchyNet_decode_encode_bhist readback,
        regularCauchyNet_decode_encode_bhist sealRow,
        regularCauchyNet_decode_encode_bhist transport,
        regularCauchyNet_decode_encode_bhist replay,
        regularCauchyNet_decode_encode_bhist provenance,
        regularCauchyNet_decode_encode_bhist localName]

private theorem regularCauchyNetToEventFlow_injective {x y : RegularCauchyNetToken} :
    regularCauchyNetToEventFlow x = regularCauchyNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) =
        regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow y) :=
    congrArg regularCauchyNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyNet_round_trip x).symm
      (Eq.trans hread (regularCauchyNet_round_trip y)))

private theorem regularCauchyNet_field_faithful :
    ∀ x y : RegularCauchyNetToken, regularCauchyNetFields x = regularCauchyNetFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk directed₁ tail₁ window₁ readback₁ seal₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk directed₂ tail₂ window₂ readback₂ seal₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases h
          rfl

instance regularCauchyNetBHistCarrier : BHistCarrier RegularCauchyNetToken where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNetToEventFlow
  fromEventFlow := regularCauchyNetFromEventFlow

instance regularCauchyNetChapterTasteGate : ChapterTasteGate RegularCauchyNetToken where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) = some x
    exact regularCauchyNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNetToEventFlow_injective heq)

instance regularCauchyNetFieldFaithful : FieldFaithful RegularCauchyNetToken where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyNetFields
  field_faithful := regularCauchyNet_field_faithful

instance regularCauchyNetNontrivial : Nontrivial RegularCauchyNetToken where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyNetToken.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyNetToken.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyNetToken :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyNetChapterTasteGate

theorem RegularCauchyNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyNetToken) ∧
        Nonempty (ChapterTasteGate RegularCauchyNetToken) ∧
          regularCauchyNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyNet_decode_encode_bhist
  · constructor
    · exact Nonempty.intro regularCauchyNetBHistCarrier
    · constructor
      · exact Nonempty.intro regularCauchyNetChapterTasteGate
      · rfl

end BEDC.Derived.RegularCauchyNetUp.TasteGate
