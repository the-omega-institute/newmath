import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionBoundaryUp : Type where
  | mk (metricCompletion uniformCompletion streamName dyadicLedger regularReadback realSeal
      transport replay provenance localName : BHist) : CauchyCompletionBoundaryUp
  deriving DecidableEq

def cauchyCompletionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionBoundaryEncodeBHist h

def cauchyCompletionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionBoundaryDecodeBHist tail)

private theorem CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionBoundaryDecodeBHist (cauchyCompletionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyCompletionBoundaryTasteGate_single_carrier_alignment_fields :
    CauchyCompletionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionBoundaryUp.mk metricCompletion uniformCompletion streamName dyadicLedger
      regularReadback realSeal transport replay provenance localName =>
      [metricCompletion, uniformCompletion, streamName, dyadicLedger, regularReadback, realSeal,
        transport, replay, provenance, localName]

def CauchyCompletionBoundaryTasteGate_single_carrier_alignment_toEventFlow :
    CauchyCompletionBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyCompletionBoundaryTasteGate_single_carrier_alignment_fields x).map
      cauchyCompletionBoundaryEncodeBHist

def CauchyCompletionBoundaryTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | metricCompletion :: uniformCompletion :: streamName :: dyadicLedger :: regularReadback ::
        realSeal :: transport :: replay :: provenance :: localName :: [] =>
      some
        (CauchyCompletionBoundaryUp.mk
          (cauchyCompletionBoundaryDecodeBHist metricCompletion)
          (cauchyCompletionBoundaryDecodeBHist uniformCompletion)
          (cauchyCompletionBoundaryDecodeBHist streamName)
          (cauchyCompletionBoundaryDecodeBHist dyadicLedger)
          (cauchyCompletionBoundaryDecodeBHist regularReadback)
          (cauchyCompletionBoundaryDecodeBHist realSeal)
          (cauchyCompletionBoundaryDecodeBHist transport)
          (cauchyCompletionBoundaryDecodeBHist replay)
          (cauchyCompletionBoundaryDecodeBHist provenance)
              (cauchyCompletionBoundaryDecodeBHist localName))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def CauchyCompletionBoundaryTasteGate_single_carrier_alignment_carrier :
    BHistCarrier CauchyCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyCompletionBoundaryTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyCompletionBoundaryTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyCompletionBoundaryTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyCompletionBoundaryTasteGate_single_carrier_alignment_carrier

private theorem CauchyCompletionBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionBoundaryUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk metricCompletion uniformCompletion streamName dyadicLedger regularReadback realSeal
      transport replay provenance localName =>
      change
        some
            (CauchyCompletionBoundaryUp.mk
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist metricCompletion))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist uniformCompletion))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist streamName))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist dyadicLedger))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist regularReadback))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist realSeal))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist transport))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist replay))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist provenance))
              (cauchyCompletionBoundaryDecodeBHist
                (cauchyCompletionBoundaryEncodeBHist localName))) =
          some
            (CauchyCompletionBoundaryUp.mk metricCompletion uniformCompletion streamName
              dyadicLedger regularReadback realSeal transport replay provenance localName)
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode
        metricCompletion]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode
        uniformCompletion]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode streamName]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode dyadicLedger]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode
        regularReadback]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode realSeal]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode transport]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode replay]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyCompletionBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionBoundaryUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (CauchyCompletionBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := CauchyCompletionBoundaryTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def CauchyCompletionBoundaryTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate CauchyCompletionBoundaryUp
      CauchyCompletionBoundaryTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact CauchyCompletionBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CauchyCompletionBoundaryTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyCompletionBoundaryTasteGate_single_carrier_alignment_gate

theorem CauchyCompletionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletionBoundaryDecodeBHist (cauchyCompletionBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionBoundaryUp) ∧
      Nonempty (ChapterTasteGate CauchyCompletionBoundaryUp) ∧
      cauchyCompletionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionBoundaryTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨CauchyCompletionBoundaryTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨CauchyCompletionBoundaryTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.CauchyCompletionBoundaryUp
