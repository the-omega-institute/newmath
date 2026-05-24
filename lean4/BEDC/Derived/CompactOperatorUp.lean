import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive CompactOperatorUp : Type where
  | compactOperator : CompactOperatorUp

def CompactOperatorCarrier [AskSetup] [PackageSetup]
    (source target operator imageNet modulus transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
    UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont source target operator ∧ Cont operator imageNet modulus ∧
          Cont provenance transport localName ∧ PkgSig bundle localName pkg

theorem CompactOperatorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont operator imageNet consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
            UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory consumer ∧
              Cont source target operator ∧ Cont operator imageNet modulus ∧
                Cont operator imageNet consumer ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageNetConsumer consumerPkg
  obtain ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, sourceTargetOperator,
    operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageNetConsumer
  exact
    ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary, consumerUnary,
      sourceTargetOperator, operatorImageNetModulus, operatorImageNetConsumer, localNamePkg,
      consumerPkg⟩

end BEDC.Derived
