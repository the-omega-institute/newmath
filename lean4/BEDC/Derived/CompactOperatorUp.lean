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

theorem CompactOperatorCarrier_bounded_image_precompactness [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      precompactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont compactRead modulus precompactRead ->
          PkgSig bundle precompactRead pkg ->
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
              UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory compactRead ∧
                UnaryHistory precompactRead ∧ Cont operator imageNet compactRead ∧
                  Cont compactRead modulus precompactRead ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle precompactRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageNetCompact compactModulusPrecompact precompactPkg
  obtain ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageNetCompact
  have precompactUnary : UnaryHistory precompactRead :=
    unary_cont_closed compactUnary modulusUnary compactModulusPrecompact
  exact
    ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary, compactUnary,
      precompactUnary, operatorImageNetCompact, compactModulusPrecompact, localNamePkg,
      precompactPkg⟩

theorem CompactOperatorCarrier_ideal_consumer_boundary [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      idealRead nuclearRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont compactRead provenance idealRead ->
          Cont idealRead replay nuclearRead ->
            PkgSig bundle idealRead pkg ->
              PkgSig bundle nuclearRead pkg ->
                UnaryHistory compactRead ∧ UnaryHistory idealRead ∧
                  UnaryHistory nuclearRead ∧ Cont operator imageNet compactRead ∧
                    Cont compactRead provenance idealRead ∧ Cont idealRead replay nuclearRead ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle idealRead pkg ∧
                        PkgSig bundle nuclearRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageNetCompact compactProvenanceIdeal idealReplayNuclear idealPkg
    nuclearPkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, _modulusUnary,
    _transportUnary, replayUnary, provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageNetCompact
  have idealUnary : UnaryHistory idealRead :=
    unary_cont_closed compactUnary provenanceUnary compactProvenanceIdeal
  have nuclearUnary : UnaryHistory nuclearRead :=
    unary_cont_closed idealUnary replayUnary idealReplayNuclear
  exact
    ⟨compactUnary, idealUnary, nuclearUnary, operatorImageNetCompact, compactProvenanceIdeal,
      idealReplayNuclear, localNamePkg, idealPkg, nuclearPkg⟩

theorem CompactOperatorCarrier_tail_modulus_consumer_exactness [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName tailRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont imageNet modulus tailRead ->
        Cont tailRead transport terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory transport ∧
              UnaryHistory tailRead ∧ UnaryHistory terminalRead ∧
                Cont imageNet modulus tailRead ∧ Cont tailRead transport terminalRead ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier imageNetModulusTail tailTransportTerminal terminalPkg
  obtain ⟨_sourceUnary, _targetUnary, _operatorUnary, imageNetUnary, modulusUnary,
    transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed imageNetUnary modulusUnary imageNetModulusTail
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed tailUnary transportUnary tailTransportTerminal
  exact
    ⟨imageNetUnary, modulusUnary, transportUnary, tailUnary, terminalUnary,
      imageNetModulusTail, tailTransportTerminal, localNamePkg, terminalPkg⟩

theorem CompactOperatorCarrier_finite_rank_approximation_boundary [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      finiteRankRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont compactRead modulus finiteRankRead ->
          PkgSig bundle finiteRankRead pkg ->
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
              UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory compactRead ∧
                UnaryHistory finiteRankRead ∧ Cont source target operator ∧
                  Cont operator imageNet compactRead ∧ Cont compactRead modulus finiteRankRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle finiteRankRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageNetCompact compactModulusFiniteRank finiteRankPkg
  obtain ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageNetCompact
  have finiteRankUnary : UnaryHistory finiteRankRead :=
    unary_cont_closed compactUnary modulusUnary compactModulusFiniteRank
  exact
    ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary, compactUnary,
      finiteRankUnary, sourceTargetOperator, operatorImageNetCompact, compactModulusFiniteRank,
      localNamePkg, finiteRankPkg⟩

theorem CompactOperatorCarrier_spectral_refusal_boundary [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      spectralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorCarrier source target operator imageNet modulus transport replay provenance
        localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont provenance replay spectralRead ->
          PkgSig bundle compactRead pkg ->
            PkgSig bundle spectralRead pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory operator ∧
                UnaryHistory imageNet ∧ UnaryHistory modulus ∧ UnaryHistory compactRead ∧
                  UnaryHistory spectralRead ∧ Cont operator imageNet compactRead ∧
                    Cont provenance replay spectralRead ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle compactRead pkg ∧ PkgSig bundle spectralRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier operatorImageNetCompact provenanceReplaySpectral compactPkg spectralPkg
  obtain ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, replayUnary, provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary operatorImageNetCompact
  have spectralUnary : UnaryHistory spectralRead :=
    unary_cont_closed provenanceUnary replayUnary provenanceReplaySpectral
  exact
    ⟨sourceUnary, targetUnary, operatorUnary, imageNetUnary, modulusUnary, compactUnary,
      spectralUnary, operatorImageNetCompact, provenanceReplaySpectral, localNamePkg,
      compactPkg, spectralPkg⟩

end BEDC.Derived
