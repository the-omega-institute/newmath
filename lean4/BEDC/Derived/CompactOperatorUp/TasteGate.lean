import BEDC.Derived.CompactOperatorUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactOperatorCarrier_functional_analysis_route [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName consumer
      idealRead nuclearRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg →
      Cont operator imageNet consumer →
        UnaryHistory idealRead →
          Cont consumer idealRead nuclearRead →
            PkgSig bundle consumer pkg →
              UnaryHistory consumer ∧
                UnaryHistory nuclearRead ∧
                  Cont operator imageNet consumer ∧
                    Cont consumer idealRead nuclearRead ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageConsumer idealUnary consumerIdealNuclear consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, _modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _sourceTargetOperator, _operatorImageModulus, _provenanceTransportLocalName,
    localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageConsumer
  have nuclearUnary : UnaryHistory nuclearRead :=
    unary_cont_closed consumerUnary idealUnary consumerIdealNuclear
  exact
    ⟨consumerUnary, nuclearUnary, operatorImageConsumer, consumerIdealNuclear,
      localNamePkg, consumerPkg⟩

end BEDC.Derived

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOperatorEncodeBHist h

def compactOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOperatorDecodeBHist tail)

private theorem CompactOperatorTasteGate_single_carrier_alignment_decode :
    forall h : BHist, compactOperatorDecodeBHist (compactOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOperatorToEventFlow : CompactOperatorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOperatorUp.compactOperator => [[BMark.b0]]

def compactOperatorFromEventFlow : EventFlow -> Option CompactOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | _ => some CompactOperatorUp.compactOperator

private theorem CompactOperatorTasteGate_single_carrier_alignment_round_trip :
    forall x : CompactOperatorUp, compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem CompactOperatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactOperatorUp} :
    compactOperatorToEventFlow x = compactOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

private theorem CompactOperatorTasteGate_single_carrier_alignment_empty_encode :
    compactOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

instance compactOperatorBHistCarrier : BHistCarrier CompactOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOperatorToEventFlow
  fromEventFlow := compactOperatorFromEventFlow

instance compactOperatorChapterTasteGate : ChapterTasteGate CompactOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x
    exact CompactOperatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactOperatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactOperatorTasteGate_single_carrier_alignment :
    (forall h : BHist, compactOperatorDecodeBHist (compactOperatorEncodeBHist h) = h) ∧
      (forall x : CompactOperatorUp,
        compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x) ∧
        (forall x y : CompactOperatorUp,
          compactOperatorToEventFlow x = compactOperatorToEventFlow y -> x = y) ∧
          Nonempty (ChapterTasteGate CompactOperatorUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactOperatorTasteGate_single_carrier_alignment_decode,
      CompactOperatorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactOperatorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨compactOperatorChapterTasteGate⟩⟩

end BEDC.Derived.CompactOperatorUp
