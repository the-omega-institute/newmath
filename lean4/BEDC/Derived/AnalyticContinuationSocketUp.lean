import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive AnalyticContinuationSocketUp : Type where
  | mk
      (source leftOverlap witness operation output branch transport continuation provenance name :
        BHist) :
      AnalyticContinuationSocketUp

def AnalyticContinuationSocketCarrier [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
      UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source leftOverlap witness ∧ Cont witness operation output ∧
          Cont branch transport continuation ∧ Cont output continuation provenance ∧
            Cont continuation name provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem AnalyticContinuationSocketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
            UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
              UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
                UnaryHistory name ∧ UnaryHistory consumer ∧ Cont source leftOverlap witness ∧
                  Cont witness operation output ∧ Cont branch transport continuation ∧
                    Cont continuation name provenance ∧ Cont output branch consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                          (fun row : BHist => hsame row provenance)
                          (fun row : BHist => hsame row provenance ∧
                            PkgSig bundle provenance pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg
  intro carrier consumerRow consumerPkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, operationUnary, outputUnary, branchUnary,
    transportUnary, continuationUnary, provenanceUnary, nameUnary, sourceOverlapWitness,
    witnessOperationOutput, branchTransportContinuation, _outputContinuationProvenance,
    continuationNameProvenance, provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary branchUnary consumerRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance
        (And.intro (hsame_refl provenance) provenanceUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left)
          (unary_transport sourceRow.right same)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    And.intro sourceUnary
      (And.intro leftOverlapUnary
        (And.intro witnessUnary
          (And.intro operationUnary
            (And.intro outputUnary
              (And.intro branchUnary
                (And.intro transportUnary
                  (And.intro continuationUnary
                    (And.intro provenanceUnary
                      (And.intro nameUnary
                        (And.intro consumerUnary
                          (And.intro sourceOverlapWitness
                            (And.intro witnessOperationOutput
                              (And.intro branchTransportContinuation
                                (And.intro continuationNameProvenance
                                  (And.intro consumerRow
                                    (And.intro provenancePkg
                                      (And.intro consumerPkg cert)))))))))))))))))

theorem AnalyticContinuationSocketCarrier_operation_output_factorization [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory output ∧ UnaryHistory consumer ∧ Cont witness operation output ∧
            Cont output continuation consumer ∧ Cont output continuation provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier outputContinuationConsumer consumerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    _branchUnary, _transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
    outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary continuationUnary outputContinuationConsumer
  exact
    ⟨outputUnary,
      consumerUnary,
      witnessOperationOutput,
      outputContinuationConsumer,
      outputContinuationProvenance,
      provenancePkg,
      consumerPkg⟩

theorem AnalyticContinuationSocketCarrier_branch_ledger_exactness [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch consumer →
        Cont consumer transport boundary →
          PkgSig bundle boundary pkg →
            UnaryHistory branch ∧ UnaryHistory consumer ∧ UnaryHistory boundary ∧
              Cont output branch consumer ∧ Cont consumer transport boundary ∧
                Cont branch transport continuation ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier outputBranchConsumer consumerTransportBoundary boundaryPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary branchUnary outputBranchConsumer
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed consumerUnary transportUnary consumerTransportBoundary
  exact
    ⟨branchUnary,
      consumerUnary,
      boundaryUnary,
      outputBranchConsumer,
      consumerTransportBoundary,
      branchTransportContinuation,
      provenancePkg,
      boundaryPkg⟩

theorem AnalyticContinuationSocketCarrier_branch_ledger_exhaustion [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame consumer branch →
        UnaryHistory consumer ∧ UnaryHistory branch ∧ Cont branch transport continuation ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameConsumerBranch
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, _outputUnary,
    branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_transport branchUnary (hsame_symm sameConsumerBranch)
  exact
    ⟨consumerUnary,
      branchUnary,
      branchTransportContinuation,
      provenancePkg⟩

theorem AnalyticContinuationSocketCarrier_rh_handoff_boundary [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation consumer →
        Cont consumer branch boundary →
          PkgSig bundle boundary pkg →
            UnaryHistory source ∧ UnaryHistory witness ∧ UnaryHistory output ∧
              UnaryHistory consumer ∧ UnaryHistory boundary ∧ Cont witness operation output ∧
                Cont output continuation consumer ∧ Cont consumer branch boundary ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier outputContinuationConsumer consumerBranchBoundary boundaryPkg
  obtain ⟨sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, _transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary continuationUnary outputContinuationConsumer
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed consumerUnary branchUnary consumerBranchBoundary
  exact
    ⟨sourceUnary,
      witnessUnary,
      outputUnary,
      consumerUnary,
      boundaryUnary,
      witnessOperationOutput,
      outputContinuationConsumer,
      consumerBranchBoundary,
      provenancePkg,
      boundaryPkg⟩

def AnalyticContinuationSocketPacket [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
      UnaryHistory provenance ∧ Cont source leftOverlap transport ∧
        Cont witness operation continuation ∧ PkgSig bundle name pkg

theorem AnalyticContinuationSocketPacket_overlap_transport [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketPacket source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
        Cont source leftOverlap transport ∧ Cont witness operation continuation ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, _operationUnary, _outputUnary,
    _branchUnary, _provenanceUnary, overlapRoute, continuationRoute, namePkg⟩ := packet
  exact
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, overlapRoute, continuationRoute, namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
