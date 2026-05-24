import BEDC.Derived.CompactOperatorUp

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
