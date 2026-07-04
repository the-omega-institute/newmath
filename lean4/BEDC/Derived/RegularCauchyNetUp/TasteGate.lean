import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNetUp : Type where
  | mk
      (directed tail window readback sealRow transport replay provenance localName : BHist) :
      RegularCauchyNetUp
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

private theorem regularCauchyNetDecode_encode_bhist :
    ∀ h : BHist, regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyNetToEventFlow : RegularCauchyNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNetUp.mk directed tail window readback sealRow transport replay provenance
      localName =>
      [regularCauchyNetEncodeBHist directed,
        regularCauchyNetEncodeBHist tail,
        regularCauchyNetEncodeBHist window,
        regularCauchyNetEncodeBHist readback,
        regularCauchyNetEncodeBHist sealRow,
        regularCauchyNetEncodeBHist transport,
        regularCauchyNetEncodeBHist replay,
        regularCauchyNetEncodeBHist provenance,
        regularCauchyNetEncodeBHist localName]

def regularCauchyNetFromEventFlow : EventFlow → Option RegularCauchyNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | directed :: rest0 =>
      match rest0 with
      | tail :: rest1 =>
          match rest1 with
          | window :: rest2 =>
              match rest2 with
              | readback :: rest3 =>
                  match rest3 with
                  | sealRow :: rest4 =>
                      match rest4 with
                      | transport :: rest5 =>
                          match rest5 with
                          | replay :: rest6 =>
                              match rest6 with
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RegularCauchyNetUp.mk
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
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem regularCauchyNet_round_trip :
    ∀ x : RegularCauchyNetUp,
      regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk directed tail window readback sealRow transport replay provenance localName =>
      change
        some
          (RegularCauchyNetUp.mk
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
            (RegularCauchyNetUp.mk directed tail window readback sealRow transport replay
              provenance localName)
      rw [regularCauchyNetDecode_encode_bhist directed,
        regularCauchyNetDecode_encode_bhist tail,
        regularCauchyNetDecode_encode_bhist window,
        regularCauchyNetDecode_encode_bhist readback,
        regularCauchyNetDecode_encode_bhist sealRow,
        regularCauchyNetDecode_encode_bhist transport,
        regularCauchyNetDecode_encode_bhist replay,
        regularCauchyNetDecode_encode_bhist provenance,
        regularCauchyNetDecode_encode_bhist localName]

private theorem regularCauchyNetToEventFlow_injective {x y : RegularCauchyNetUp} :
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

instance regularCauchyNetBHistCarrier : BHistCarrier RegularCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNetToEventFlow
  fromEventFlow := regularCauchyNetFromEventFlow

instance regularCauchyNetChapterTasteGate : ChapterTasteGate RegularCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) = some x
    exact regularCauchyNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNetToEventFlow_injective heq)

theorem RegularCauchyNetTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyNetUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyNetUp) ∧
        (∀ h : BHist, regularCauchyNetDecodeBHist (regularCauchyNetEncodeBHist h) = h) ∧
          (∀ x : RegularCauchyNetUp,
            regularCauchyNetFromEventFlow (regularCauchyNetToEventFlow x) = some x) ∧
            regularCauchyNetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro regularCauchyNetBHistCarrier
  · constructor
    · exact Nonempty.intro regularCauchyNetChapterTasteGate
    · constructor
      · exact regularCauchyNetDecode_encode_bhist
      · constructor
        · exact regularCauchyNet_round_trip
        · rfl

end BEDC.Derived.RegularCauchyNetUp
