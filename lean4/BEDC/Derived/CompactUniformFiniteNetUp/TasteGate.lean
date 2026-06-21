import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformFiniteNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformFiniteNetUp : Type where
  | mk (compactSource metricDistance continuousSource probeBundle centerCoverage radiusLedger
      lowerBoundFold uniformHandoff transport replay provenance localName :
      BHist) : CompactUniformFiniteNetUp
  deriving DecidableEq

def compactUniformFiniteNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformFiniteNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformFiniteNetEncodeBHist h

def compactUniformFiniteNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformFiniteNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformFiniteNetDecodeBHist tail)

private theorem CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactUniformFiniteNetDecodeBHist (compactUniformFiniteNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactUniformFiniteNetTasteGate_single_carrier_alignment_fields :
    CompactUniformFiniteNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformFiniteNetUp.mk compactSource metricDistance continuousSource probeBundle
      centerCoverage radiusLedger lowerBoundFold uniformHandoff transport replay provenance
      localName =>
      [compactSource, metricDistance, continuousSource, probeBundle, centerCoverage,
        radiusLedger, lowerBoundFold, uniformHandoff, transport, replay, provenance, localName]

def CompactUniformFiniteNetTasteGate_single_carrier_alignment_toEventFlow :
    CompactUniformFiniteNetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CompactUniformFiniteNetTasteGate_single_carrier_alignment_fields x).map
      compactUniformFiniteNetEncodeBHist

def CompactUniformFiniteNetTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CompactUniformFiniteNetUp
  -- BEDC touchpoint anchor: BHist BMark
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
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | compactSource :: metricDistance :: continuousSource :: probeBundle :: centerCoverage ::
      radiusLedger :: lowerBoundFold :: uniformHandoff :: transport :: replay :: provenance ::
      localName :: [] =>
      some
        (CompactUniformFiniteNetUp.mk
          (compactUniformFiniteNetDecodeBHist compactSource)
          (compactUniformFiniteNetDecodeBHist metricDistance)
          (compactUniformFiniteNetDecodeBHist continuousSource)
          (compactUniformFiniteNetDecodeBHist probeBundle)
          (compactUniformFiniteNetDecodeBHist centerCoverage)
          (compactUniformFiniteNetDecodeBHist radiusLedger)
          (compactUniformFiniteNetDecodeBHist lowerBoundFold)
          (compactUniformFiniteNetDecodeBHist uniformHandoff)
          (compactUniformFiniteNetDecodeBHist transport)
          (compactUniformFiniteNetDecodeBHist replay)
          (compactUniformFiniteNetDecodeBHist provenance)
          (compactUniformFiniteNetDecodeBHist localName))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier :
    BHistCarrier CompactUniformFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactUniformFiniteNetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompactUniformFiniteNetTasteGate_single_carrier_alignment_fromEventFlow

instance CompactUniformFiniteNetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CompactUniformFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier

private theorem CompactUniformFiniteNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformFiniteNetUp,
      @BHistCarrier.fromEventFlow CompactUniformFiniteNetUp
          CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier
          (@BHistCarrier.toEventFlow CompactUniformFiniteNetUp
            CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk compactSource metricDistance continuousSource probeBundle centerCoverage radiusLedger
      lowerBoundFold uniformHandoff transport replay provenance localName =>
      change
        some
            (CompactUniformFiniteNetUp.mk
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist compactSource))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist metricDistance))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist continuousSource))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist probeBundle))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist centerCoverage))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist radiusLedger))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist lowerBoundFold))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist uniformHandoff))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist transport))
              (compactUniformFiniteNetDecodeBHist (compactUniformFiniteNetEncodeBHist replay))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist provenance))
              (compactUniformFiniteNetDecodeBHist
                (compactUniformFiniteNetEncodeBHist localName))) =
          some
            (CompactUniformFiniteNetUp.mk compactSource metricDistance continuousSource
              probeBundle centerCoverage radiusLedger lowerBoundFold uniformHandoff transport
              replay provenance localName)
      rw [CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode compactSource,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode metricDistance,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode continuousSource,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode probeBundle,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode centerCoverage,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode radiusLedger,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode lowerBoundFold,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode uniformHandoff,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode transport,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode replay,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode provenance,
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CompactUniformFiniteNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformFiniteNetUp} :
    @BHistCarrier.toEventFlow CompactUniformFiniteNetUp
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier x =
      @BHistCarrier.toEventFlow CompactUniformFiniteNetUp
        CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          @BHistCarrier.fromEventFlow CompactUniformFiniteNetUp
              CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow CompactUniformFiniteNetUp
                CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier x) :=
        (CompactUniformFiniteNetTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          @BHistCarrier.fromEventFlow CompactUniformFiniteNetUp
              CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow CompactUniformFiniteNetUp
                CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier y) :=
        congrArg
          (@BHistCarrier.fromEventFlow CompactUniformFiniteNetUp
            CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier) hxy
      _ = some y := CompactUniformFiniteNetTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def CompactUniformFiniteNetTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate CompactUniformFiniteNetUp
      CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact CompactUniformFiniteNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactUniformFiniteNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CompactUniformFiniteNetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CompactUniformFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CompactUniformFiniteNetTasteGate_single_carrier_alignment_gate

theorem CompactUniformFiniteNetTasteGate_single_carrier_alignment :
    (forall h : BHist, compactUniformFiniteNetDecodeBHist
      (compactUniformFiniteNetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactUniformFiniteNetUp) ∧
      Nonempty (ChapterTasteGate CompactUniformFiniteNetUp) ∧
      compactUniformFiniteNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformFiniteNetTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨CompactUniformFiniteNetTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨CompactUniformFiniteNetTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.CompactUniformFiniteNetUp
