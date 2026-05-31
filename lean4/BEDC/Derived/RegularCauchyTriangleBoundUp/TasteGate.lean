import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTriangleBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTriangleBoundUp : Type where
  | mk :
      (diagLeft diagRight intermediateLeft intermediateRight tolerance endpointLegs middleLeg
        transport replay provenance nameCert : BHist) ->
        RegularCauchyTriangleBoundUp
  deriving DecidableEq

def regularCauchyTriangleBoundEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTriangleBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTriangleBoundEncodeBHist h

def regularCauchyTriangleBoundDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTriangleBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTriangleBoundDecodeBHist tail)

theorem RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyTriangleBoundDecodeBHist (regularCauchyTriangleBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTriangleBoundFields : RegularCauchyTriangleBoundUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTriangleBoundUp.mk diagLeft diagRight intermediateLeft intermediateRight
      tolerance endpointLegs middleLeg transport replay provenance nameCert =>
      [diagLeft, diagRight, intermediateLeft, intermediateRight, tolerance, endpointLegs,
        middleLeg, transport, replay, provenance, nameCert]

def regularCauchyTriangleBoundToEventFlow : RegularCauchyTriangleBoundUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTriangleBoundFields x).map regularCauchyTriangleBoundEncodeBHist

def regularCauchyTriangleBoundFromEventFlow : EventFlow -> Option RegularCauchyTriangleBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | diagLeft :: diagRight :: intermediateLeft :: intermediateRight :: tolerance ::
      endpointLegs :: middleLeg :: transport :: replay :: provenance :: nameCert :: [] =>
      some
        (RegularCauchyTriangleBoundUp.mk
          (regularCauchyTriangleBoundDecodeBHist diagLeft)
          (regularCauchyTriangleBoundDecodeBHist diagRight)
          (regularCauchyTriangleBoundDecodeBHist intermediateLeft)
          (regularCauchyTriangleBoundDecodeBHist intermediateRight)
          (regularCauchyTriangleBoundDecodeBHist tolerance)
          (regularCauchyTriangleBoundDecodeBHist endpointLegs)
          (regularCauchyTriangleBoundDecodeBHist middleLeg)
          (regularCauchyTriangleBoundDecodeBHist transport)
          (regularCauchyTriangleBoundDecodeBHist replay)
          (regularCauchyTriangleBoundDecodeBHist provenance)
          (regularCauchyTriangleBoundDecodeBHist nameCert))
  | _ => none

private theorem regularCauchyTriangleBound_round_trip :
    forall x : RegularCauchyTriangleBoundUp,
      regularCauchyTriangleBoundFromEventFlow (regularCauchyTriangleBoundToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diagLeft diagRight intermediateLeft intermediateRight tolerance endpointLegs middleLeg
      transport replay provenance nameCert =>
      change
        some
          (RegularCauchyTriangleBoundUp.mk
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist diagLeft))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist diagRight))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist intermediateLeft))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist intermediateRight))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist tolerance))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist endpointLegs))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist middleLeg))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist transport))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist replay))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist provenance))
            (regularCauchyTriangleBoundDecodeBHist
              (regularCauchyTriangleBoundEncodeBHist nameCert))) =
          some
            (RegularCauchyTriangleBoundUp.mk diagLeft diagRight intermediateLeft
              intermediateRight tolerance endpointLegs middleLeg transport replay provenance
              nameCert)
      rw [RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode diagLeft,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode diagRight,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode
          intermediateLeft,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode
          intermediateRight,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode tolerance,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode endpointLegs,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode middleLeg,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode transport,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode replay,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode provenance,
        RegularCauchyTriangleBoundTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem regularCauchyTriangleBound_toEventFlow_injective
    {x y : RegularCauchyTriangleBoundUp} :
    regularCauchyTriangleBoundToEventFlow x = regularCauchyTriangleBoundToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTriangleBoundFromEventFlow (regularCauchyTriangleBoundToEventFlow x) =
        regularCauchyTriangleBoundFromEventFlow (regularCauchyTriangleBoundToEventFlow y) :=
    congrArg regularCauchyTriangleBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTriangleBound_round_trip x).symm
      (Eq.trans hread (regularCauchyTriangleBound_round_trip y)))

private theorem regularCauchyTriangleBound_field_faithful :
    forall x y : RegularCauchyTriangleBoundUp,
      regularCauchyTriangleBoundFields x = regularCauchyTriangleBoundFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk diagLeft₁ diagRight₁ intermediateLeft₁ intermediateRight₁ tolerance₁ endpointLegs₁
      middleLeg₁ transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk diagLeft₂ diagRight₂ intermediateLeft₂ intermediateRight₂ tolerance₂ endpointLegs₂
          middleLeg₂ transport₂ replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance regularCauchyTriangleBoundBHistCarrier : BHistCarrier RegularCauchyTriangleBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTriangleBoundToEventFlow
  fromEventFlow := regularCauchyTriangleBoundFromEventFlow

instance regularCauchyTriangleBoundChapterTasteGate :
    ChapterTasteGate RegularCauchyTriangleBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => regularCauchyTriangleBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTriangleBound_toEventFlow_injective heq)

instance regularCauchyTriangleBoundFieldFaithful : FieldFaithful RegularCauchyTriangleBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTriangleBoundFields
  field_faithful := regularCauchyTriangleBound_field_faithful

instance regularCauchyTriangleBoundNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyTriangleBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTriangleBoundUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTriangleBoundUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def regularCauchyTriangleBoundTasteGate : ChapterTasteGate RegularCauchyTriangleBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTriangleBoundChapterTasteGate

end BEDC.Derived.RegularCauchyTriangleBoundUp
