import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadialWobbleSpectrumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RadialWobbleSpectrumUp : Type where
  | mk
      (boundaryTile radialShell spectralHinge wobbleEdge triggerLedger metricRead
        substrateTrace transportReplay provenance localName : BHist) :
      RadialWobbleSpectrumUp
  deriving DecidableEq

def radialWobbleSpectrumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radialWobbleSpectrumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radialWobbleSpectrumEncodeBHist h

def radialWobbleSpectrumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radialWobbleSpectrumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radialWobbleSpectrumDecodeBHist tail)

private theorem radialWobbleSpectrum_decode_encode_bhist :
    ∀ h : BHist, radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radialWobbleSpectrumFields : RadialWobbleSpectrumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RadialWobbleSpectrumUp.mk boundaryTile radialShell spectralHinge wobbleEdge triggerLedger
      metricRead substrateTrace transportReplay provenance localName =>
      [boundaryTile, radialShell, spectralHinge, wobbleEdge, triggerLedger, metricRead,
        substrateTrace, transportReplay, provenance, localName]

def radialWobbleSpectrumToEventFlow : RadialWobbleSpectrumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (radialWobbleSpectrumFields x).map radialWobbleSpectrumEncodeBHist

private def radialWobbleSpectrumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => radialWobbleSpectrumEventAtDefault index rest

def radialWobbleSpectrumFromEventFlow : EventFlow → Option RadialWobbleSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RadialWobbleSpectrumUp.mk
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 0 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 1 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 2 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 3 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 4 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 5 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 6 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 7 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 8 ef))
        (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEventAtDefault 9 ef)))

private theorem radialWobbleSpectrum_round_trip :
    ∀ x : RadialWobbleSpectrumUp,
      radialWobbleSpectrumFromEventFlow (radialWobbleSpectrumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundaryTile radialShell spectralHinge wobbleEdge triggerLedger metricRead substrateTrace
      transportReplay provenance localName =>
      change
        some
          (RadialWobbleSpectrumUp.mk
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist boundaryTile))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist radialShell))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist spectralHinge))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist wobbleEdge))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist triggerLedger))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist metricRead))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist substrateTrace))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist transportReplay))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist provenance))
            (radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist localName))) =
          some
            (RadialWobbleSpectrumUp.mk boundaryTile radialShell spectralHinge wobbleEdge
              triggerLedger metricRead substrateTrace transportReplay provenance localName)
      rw [radialWobbleSpectrum_decode_encode_bhist boundaryTile,
        radialWobbleSpectrum_decode_encode_bhist radialShell,
        radialWobbleSpectrum_decode_encode_bhist spectralHinge,
        radialWobbleSpectrum_decode_encode_bhist wobbleEdge,
        radialWobbleSpectrum_decode_encode_bhist triggerLedger,
        radialWobbleSpectrum_decode_encode_bhist metricRead,
        radialWobbleSpectrum_decode_encode_bhist substrateTrace,
        radialWobbleSpectrum_decode_encode_bhist transportReplay,
        radialWobbleSpectrum_decode_encode_bhist provenance,
        radialWobbleSpectrum_decode_encode_bhist localName]

private theorem radialWobbleSpectrumToEventFlow_injective {x y : RadialWobbleSpectrumUp} :
    radialWobbleSpectrumToEventFlow x = radialWobbleSpectrumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      radialWobbleSpectrumFromEventFlow (radialWobbleSpectrumToEventFlow x) =
        radialWobbleSpectrumFromEventFlow (radialWobbleSpectrumToEventFlow y) :=
    congrArg radialWobbleSpectrumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (radialWobbleSpectrum_round_trip x).symm
      (Eq.trans hread (radialWobbleSpectrum_round_trip y)))

private theorem radialWobbleSpectrum_fields_faithful :
    ∀ x y : RadialWobbleSpectrumUp, radialWobbleSpectrumFields x = radialWobbleSpectrumFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundaryTile₁ radialShell₁ spectralHinge₁ wobbleEdge₁ triggerLedger₁ metricRead₁
      substrateTrace₁ transportReplay₁ provenance₁ localName₁ =>
      cases y with
      | mk boundaryTile₂ radialShell₂ spectralHinge₂ wobbleEdge₂ triggerLedger₂ metricRead₂
          substrateTrace₂ transportReplay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance radialWobbleSpectrumBHistCarrier : BHistCarrier RadialWobbleSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radialWobbleSpectrumToEventFlow
  fromEventFlow := radialWobbleSpectrumFromEventFlow

instance radialWobbleSpectrumChapterTasteGate : ChapterTasteGate RadialWobbleSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radialWobbleSpectrumFromEventFlow (radialWobbleSpectrumToEventFlow x) = some x
    exact radialWobbleSpectrum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (radialWobbleSpectrumToEventFlow_injective heq)

instance radialWobbleSpectrumFieldFaithful : FieldFaithful RadialWobbleSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := radialWobbleSpectrumFields
  field_faithful := radialWobbleSpectrum_fields_faithful

instance radialWobbleSpectrumNontrivial : Nontrivial RadialWobbleSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RadialWobbleSpectrumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RadialWobbleSpectrumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RadialWobbleSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  radialWobbleSpectrumChapterTasteGate

theorem RadialWobbleSpectrumTasteGate_single_carrier_alignment :
    (∀ h : BHist, radialWobbleSpectrumDecodeBHist (radialWobbleSpectrumEncodeBHist h) = h) ∧
      (∀ x : RadialWobbleSpectrumUp,
        radialWobbleSpectrumFromEventFlow (radialWobbleSpectrumToEventFlow x) = some x) ∧
      (∀ x y : RadialWobbleSpectrumUp,
        radialWobbleSpectrumToEventFlow x = radialWobbleSpectrumToEventFlow y → x = y) ∧
      radialWobbleSpectrumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact radialWobbleSpectrum_decode_encode_bhist
  constructor
  · exact radialWobbleSpectrum_round_trip
  constructor
  · intro x y heq
    exact radialWobbleSpectrumToEventFlow_injective heq
  · rfl

end BEDC.Derived.RadialWobbleSpectrumUp
