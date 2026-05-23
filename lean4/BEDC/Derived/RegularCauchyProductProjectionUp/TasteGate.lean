import BEDC.Derived.RegularCauchyProductProjectionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyProductProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyProductProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyProductProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyProductProjectionEncodeBHist h

def regularCauchyProductProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyProductProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyProductProjectionDecodeBHist tail)

private theorem regularCauchyProductProjection_decode_encode :
    ∀ h : BHist,
      regularCauchyProductProjectionDecodeBHist
          (regularCauchyProductProjectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyProductProjectionFields :
    BEDC.Derived.RegularCauchyProductProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.RegularCauchyProductProjectionUp.mk productPacket leftReadback
      rightReadback productModulus windows dyadicTolerance leftHandoff rightHandoff realSeal
      transport replay provenance name =>
      [productPacket, leftReadback, rightReadback, productModulus, windows, dyadicTolerance,
        leftHandoff, rightHandoff, realSeal, transport, replay, provenance, name]

def regularCauchyProductProjectionToEventFlow :
    BEDC.Derived.RegularCauchyProductProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyProductProjectionFields x).map
        regularCauchyProductProjectionEncodeBHist

def regularCauchyProductProjectionFromEventFlow :
    EventFlow → Option BEDC.Derived.RegularCauchyProductProjectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [productPacket, leftReadback, rightReadback, productModulus, windows, dyadicTolerance,
      leftHandoff, rightHandoff, realSeal, transport, replay, provenance, name] =>
      some
        (BEDC.Derived.RegularCauchyProductProjectionUp.mk
          (regularCauchyProductProjectionDecodeBHist productPacket)
          (regularCauchyProductProjectionDecodeBHist leftReadback)
          (regularCauchyProductProjectionDecodeBHist rightReadback)
          (regularCauchyProductProjectionDecodeBHist productModulus)
          (regularCauchyProductProjectionDecodeBHist windows)
          (regularCauchyProductProjectionDecodeBHist dyadicTolerance)
          (regularCauchyProductProjectionDecodeBHist leftHandoff)
          (regularCauchyProductProjectionDecodeBHist rightHandoff)
          (regularCauchyProductProjectionDecodeBHist realSeal)
          (regularCauchyProductProjectionDecodeBHist transport)
          (regularCauchyProductProjectionDecodeBHist replay)
          (regularCauchyProductProjectionDecodeBHist provenance)
          (regularCauchyProductProjectionDecodeBHist name))
  | _ => none

private theorem regularCauchyProductProjection_round_trip
    (x : BEDC.Derived.RegularCauchyProductProjectionUp) :
    regularCauchyProductProjectionFromEventFlow
        (regularCauchyProductProjectionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk productPacket leftReadback rightReadback productModulus windows dyadicTolerance
      leftHandoff rightHandoff realSeal transport replay provenance name =>
      change
        some
            (BEDC.Derived.RegularCauchyProductProjectionUp.mk
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist productPacket))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist leftReadback))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist rightReadback))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist productModulus))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist windows))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist dyadicTolerance))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist leftHandoff))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist rightHandoff))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist realSeal))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist transport))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist replay))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist provenance))
              (regularCauchyProductProjectionDecodeBHist
                (regularCauchyProductProjectionEncodeBHist name))) =
          some
            (BEDC.Derived.RegularCauchyProductProjectionUp.mk productPacket leftReadback
              rightReadback productModulus windows dyadicTolerance leftHandoff rightHandoff
              realSeal transport replay provenance name)
      rw [regularCauchyProductProjection_decode_encode productPacket,
        regularCauchyProductProjection_decode_encode leftReadback,
        regularCauchyProductProjection_decode_encode rightReadback,
        regularCauchyProductProjection_decode_encode productModulus,
        regularCauchyProductProjection_decode_encode windows,
        regularCauchyProductProjection_decode_encode dyadicTolerance,
        regularCauchyProductProjection_decode_encode leftHandoff,
        regularCauchyProductProjection_decode_encode rightHandoff,
        regularCauchyProductProjection_decode_encode realSeal,
        regularCauchyProductProjection_decode_encode transport,
        regularCauchyProductProjection_decode_encode replay,
        regularCauchyProductProjection_decode_encode provenance,
        regularCauchyProductProjection_decode_encode name]

private theorem regularCauchyProductProjectionToEventFlow_injective
    {x y : BEDC.Derived.RegularCauchyProductProjectionUp} :
    regularCauchyProductProjectionToEventFlow x =
        regularCauchyProductProjectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyProductProjectionFromEventFlow
          (regularCauchyProductProjectionToEventFlow x) =
        regularCauchyProductProjectionFromEventFlow
          (regularCauchyProductProjectionToEventFlow y) :=
    congrArg regularCauchyProductProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyProductProjection_round_trip x).symm
      (Eq.trans hread (regularCauchyProductProjection_round_trip y)))

instance regularCauchyProductProjectionBHistCarrier :
    BHistCarrier BEDC.Derived.RegularCauchyProductProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyProductProjectionToEventFlow
  fromEventFlow := regularCauchyProductProjectionFromEventFlow

instance regularCauchyProductProjectionChapterTasteGate :
    ChapterTasteGate BEDC.Derived.RegularCauchyProductProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := regularCauchyProductProjection_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyProductProjectionToEventFlow_injective heq)

def regularCauchyProductProjection_taste_gate :
    ChapterTasteGate BEDC.Derived.RegularCauchyProductProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyProductProjectionChapterTasteGate

theorem RegularCauchyProductProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyProductProjectionDecodeBHist
          (regularCauchyProductProjectionEncodeBHist h) =
        h) ∧
      regularCauchyProductProjectionFields
          (BEDC.Derived.RegularCauchyProductProjectionUp.mk BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyProductProjection_decode_encode
  · rfl

end BEDC.Derived.RegularCauchyProductProjectionUp
