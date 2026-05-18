import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWindowTransducerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWindowTransducerUp : Type where
  | mk (streamWindow dyadicTolerance windowStep regSeqReadback realSeal
      limitSelector transport continuation provenance nameCert : BHist) :
      CauchyWindowTransducerUp
  deriving DecidableEq

def cauchyWindowTransducerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWindowTransducerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWindowTransducerEncodeBHist h

def cauchyWindowTransducerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWindowTransducerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWindowTransducerDecodeBHist tail)

private theorem cauchyWindowTransducerDecode_encode_bhist :
    ∀ h : BHist,
      cauchyWindowTransducerDecodeBHist
        (cauchyWindowTransducerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyWindowTransducerFields :
    CauchyWindowTransducerUp → List BHist
  | CauchyWindowTransducerUp.mk streamWindow dyadicTolerance windowStep
      regSeqReadback realSeal limitSelector transport continuation provenance nameCert =>
      [streamWindow, dyadicTolerance, windowStep, regSeqReadback, realSeal,
        limitSelector, transport, continuation, provenance, nameCert]

def cauchyWindowTransducerToEventFlow :
    CauchyWindowTransducerUp → EventFlow
  | CauchyWindowTransducerUp.mk streamWindow dyadicTolerance windowStep
      regSeqReadback realSeal limitSelector transport continuation provenance nameCert =>
      [cauchyWindowTransducerEncodeBHist streamWindow,
        cauchyWindowTransducerEncodeBHist dyadicTolerance,
        cauchyWindowTransducerEncodeBHist windowStep,
        cauchyWindowTransducerEncodeBHist regSeqReadback,
        cauchyWindowTransducerEncodeBHist realSeal,
        cauchyWindowTransducerEncodeBHist limitSelector,
        cauchyWindowTransducerEncodeBHist transport,
        cauchyWindowTransducerEncodeBHist continuation,
        cauchyWindowTransducerEncodeBHist provenance,
        cauchyWindowTransducerEncodeBHist nameCert]

def cauchyWindowTransducerFromEventFlow :
    EventFlow → Option CauchyWindowTransducerUp
  | streamWindow :: dyadicTolerance :: windowStep :: regSeqReadback :: realSeal ::
      limitSelector :: transport :: continuation :: provenance :: nameCert :: [] =>
      some
        (CauchyWindowTransducerUp.mk
          (cauchyWindowTransducerDecodeBHist streamWindow)
          (cauchyWindowTransducerDecodeBHist dyadicTolerance)
          (cauchyWindowTransducerDecodeBHist windowStep)
          (cauchyWindowTransducerDecodeBHist regSeqReadback)
          (cauchyWindowTransducerDecodeBHist realSeal)
          (cauchyWindowTransducerDecodeBHist limitSelector)
          (cauchyWindowTransducerDecodeBHist transport)
          (cauchyWindowTransducerDecodeBHist continuation)
          (cauchyWindowTransducerDecodeBHist provenance)
          (cauchyWindowTransducerDecodeBHist nameCert))
  | _ => none

private theorem cauchyWindowTransducer_round_trip :
    ∀ x : CauchyWindowTransducerUp,
      cauchyWindowTransducerFromEventFlow
        (cauchyWindowTransducerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk streamWindow dyadicTolerance windowStep regSeqReadback realSeal
      limitSelector transport continuation provenance nameCert =>
      change
        some
            (CauchyWindowTransducerUp.mk
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist streamWindow))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist dyadicTolerance))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist windowStep))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist regSeqReadback))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist realSeal))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist limitSelector))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist transport))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist continuation))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist provenance))
              (cauchyWindowTransducerDecodeBHist
                (cauchyWindowTransducerEncodeBHist nameCert))) =
          some
            (CauchyWindowTransducerUp.mk streamWindow dyadicTolerance windowStep
              regSeqReadback realSeal limitSelector transport continuation provenance
              nameCert)
      rw [cauchyWindowTransducerDecode_encode_bhist streamWindow,
        cauchyWindowTransducerDecode_encode_bhist dyadicTolerance,
        cauchyWindowTransducerDecode_encode_bhist windowStep,
        cauchyWindowTransducerDecode_encode_bhist regSeqReadback,
        cauchyWindowTransducerDecode_encode_bhist realSeal,
        cauchyWindowTransducerDecode_encode_bhist limitSelector,
        cauchyWindowTransducerDecode_encode_bhist transport,
        cauchyWindowTransducerDecode_encode_bhist continuation,
        cauchyWindowTransducerDecode_encode_bhist provenance,
        cauchyWindowTransducerDecode_encode_bhist nameCert]

private theorem cauchyWindowTransducerToEventFlow_injective
    {x y : CauchyWindowTransducerUp}
    (h : cauchyWindowTransducerToEventFlow x =
      cauchyWindowTransducerToEventFlow y) :
    x = y := by
  have hread :
      cauchyWindowTransducerFromEventFlow (cauchyWindowTransducerToEventFlow x) =
        cauchyWindowTransducerFromEventFlow (cauchyWindowTransducerToEventFlow y) :=
    congrArg cauchyWindowTransducerFromEventFlow h
  exact Option.some.inj
    (Eq.trans (cauchyWindowTransducer_round_trip x).symm
      (Eq.trans hread (cauchyWindowTransducer_round_trip y)))

private theorem cauchyWindowTransducer_fields_faithful :
    ∀ x y : CauchyWindowTransducerUp,
      cauchyWindowTransducerFields x = cauchyWindowTransducerFields y → x = y := by
  intro x y hfields
  cases x with
  | mk streamWindow dyadicTolerance windowStep regSeqReadback realSeal
      limitSelector transport continuation provenance nameCert =>
      cases y with
      | mk streamWindow' dyadicTolerance' windowStep' regSeqReadback' realSeal'
          limitSelector' transport' continuation' provenance' nameCert' =>
          cases hfields
          rfl

instance cauchyWindowTransducerBHistCarrier :
    BHistCarrier CauchyWindowTransducerUp where
  toEventFlow := cauchyWindowTransducerToEventFlow
  fromEventFlow := cauchyWindowTransducerFromEventFlow

instance cauchyWindowTransducerChapterTasteGate :
    ChapterTasteGate CauchyWindowTransducerUp where
  round_trip := cauchyWindowTransducer_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyWindowTransducerToEventFlow_injective heq)

instance cauchyWindowTransducerFieldFaithful :
    FieldFaithful CauchyWindowTransducerUp where
  fields := cauchyWindowTransducerFields
  field_faithful := cauchyWindowTransducer_fields_faithful

instance cauchyWindowTransducerNontrivial :
    Nontrivial CauchyWindowTransducerUp where
  witness_pair :=
    ⟨CauchyWindowTransducerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyWindowTransducerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyWindowTransducerUp :=
  cauchyWindowTransducerChapterTasteGate

theorem CauchyWindowTransducerTasteGate_single_carrier_alignment :
    cauchyWindowTransducerFields
        (CauchyWindowTransducerUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty) =
      [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      cauchyWindowTransducerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
        cauchyWindowTransducerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

end BEDC.Derived.CauchyWindowTransducerUp
