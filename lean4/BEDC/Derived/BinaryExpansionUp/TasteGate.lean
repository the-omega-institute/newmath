import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinaryExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinaryExpansionUp : Type where
  | mk
      (digits windows approximation regular realSeal transport route provenance nameCert :
        BHist) :
      BinaryExpansionUp
  deriving DecidableEq

def binaryExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binaryExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binaryExpansionEncodeBHist h

def binaryExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binaryExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binaryExpansionDecodeBHist tail)

private theorem binaryExpansionDecode_encode_bhist :
    ∀ h : BHist, binaryExpansionDecodeBHist (binaryExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def binaryExpansionFields : BinaryExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryExpansionUp.mk digits windows approximation regular realSeal transport route provenance
      nameCert =>
      [digits, windows, approximation, regular, realSeal, transport, route, provenance, nameCert]

def binaryExpansionToEventFlow : BinaryExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryExpansionUp.mk digits windows approximation regular realSeal transport route provenance
      nameCert =>
      [binaryExpansionEncodeBHist digits,
        binaryExpansionEncodeBHist windows,
        binaryExpansionEncodeBHist approximation,
        binaryExpansionEncodeBHist regular,
        binaryExpansionEncodeBHist realSeal,
        binaryExpansionEncodeBHist transport,
        binaryExpansionEncodeBHist route,
        binaryExpansionEncodeBHist provenance,
        binaryExpansionEncodeBHist nameCert]

def binaryExpansionFromEventFlow : EventFlow → Option BinaryExpansionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | digits :: rest0 =>
      match rest0 with
      | windows :: rest1 =>
          match rest1 with
          | approximation :: rest2 =>
              match rest2 with
              | regular :: rest3 =>
                  match rest3 with
                  | realSeal :: rest4 =>
                      match rest4 with
                      | transport :: rest5 =>
                          match rest5 with
                          | route :: rest6 =>
                              match rest6 with
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BinaryExpansionUp.mk
                                              (binaryExpansionDecodeBHist digits)
                                              (binaryExpansionDecodeBHist windows)
                                              (binaryExpansionDecodeBHist approximation)
                                              (binaryExpansionDecodeBHist regular)
                                              (binaryExpansionDecodeBHist realSeal)
                                              (binaryExpansionDecodeBHist transport)
                                              (binaryExpansionDecodeBHist route)
                                              (binaryExpansionDecodeBHist provenance)
                                              (binaryExpansionDecodeBHist nameCert))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem binaryExpansion_round_trip :
    ∀ x : BinaryExpansionUp,
      binaryExpansionFromEventFlow (binaryExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk digits windows approximation regular realSeal transport route provenance nameCert =>
      change
        some
          (BinaryExpansionUp.mk
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist digits))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist windows))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist approximation))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist regular))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist realSeal))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist transport))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist route))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist provenance))
            (binaryExpansionDecodeBHist (binaryExpansionEncodeBHist nameCert))) =
          some
            (BinaryExpansionUp.mk digits windows approximation regular realSeal transport route
              provenance nameCert)
      rw [binaryExpansionDecode_encode_bhist digits, binaryExpansionDecode_encode_bhist windows,
        binaryExpansionDecode_encode_bhist approximation,
        binaryExpansionDecode_encode_bhist regular,
        binaryExpansionDecode_encode_bhist realSeal,
        binaryExpansionDecode_encode_bhist transport, binaryExpansionDecode_encode_bhist route,
        binaryExpansionDecode_encode_bhist provenance,
        binaryExpansionDecode_encode_bhist nameCert]

private theorem binaryExpansionToEventFlow_injective {x y : BinaryExpansionUp} :
    binaryExpansionToEventFlow x = binaryExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      binaryExpansionFromEventFlow (binaryExpansionToEventFlow x) =
        binaryExpansionFromEventFlow (binaryExpansionToEventFlow y) :=
    congrArg binaryExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (binaryExpansion_round_trip x).symm
      (Eq.trans hread (binaryExpansion_round_trip y)))

instance binaryExpansionBHistCarrier : BHistCarrier BinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := binaryExpansionToEventFlow
  fromEventFlow := binaryExpansionFromEventFlow

instance binaryExpansionChapterTasteGate : ChapterTasteGate BinaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change binaryExpansionFromEventFlow (binaryExpansionToEventFlow x) = some x
    exact binaryExpansion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (binaryExpansionToEventFlow_injective heq)

theorem BinaryExpansionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BinaryExpansionUp) ∧
      Nonempty (ChapterTasteGate BinaryExpansionUp) ∧
        (∀ h : BHist, binaryExpansionDecodeBHist (binaryExpansionEncodeBHist h) = h) ∧
          (∀ x : BinaryExpansionUp,
            binaryExpansionFromEventFlow (binaryExpansionToEventFlow x) = some x) ∧
            binaryExpansionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro binaryExpansionBHistCarrier
  · constructor
    · exact Nonempty.intro binaryExpansionChapterTasteGate
    · constructor
      · exact binaryExpansionDecode_encode_bhist
      · constructor
        · exact binaryExpansion_round_trip
        · rfl

end BEDC.Derived.BinaryExpansionUp
