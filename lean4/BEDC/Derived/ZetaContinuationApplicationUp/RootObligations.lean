import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationApplicationRowTotality [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      operationRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont application replay operationRead ->
        UnaryHistory branchRead ->
          Cont operationRead branchRead name ->
            PkgSig bundle operationRead pkg ->
              UnaryHistory gamma ∧ UnaryHistory application ∧ UnaryHistory replay ∧
                UnaryHistory operationRead ∧ UnaryHistory branchRead ∧ UnaryHistory name ∧
                  Cont gamma application replay ∧ Cont application replay operationRead ∧
                    Cont operationRead branchRead name ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle operationRead pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier applicationReplayOperation branchReadUnary operationBranchName operationPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, gammaApplicationReplay,
    provenancePkg, namePkg⟩ := carrier
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  exact
    ⟨gammaUnary, applicationUnary, replayUnary, operationReadUnary, branchReadUnary,
      nameUnary, gammaApplicationReplay, applicationReplayOperation, operationBranchName,
      provenancePkg, operationPkg, namePkg⟩

theorem ZetaContinuationApplicationRootSourceLockExhaustion [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      sourceRead gammaRead operationRead supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont operationRead provenance supportRead →
              PkgSig bundle supportRead pkg →
                UnaryHistory eta ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
                  UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory sourceRead ∧
                    UnaryHistory gammaRead ∧ UnaryHistory operationRead ∧
                      UnaryHistory supportRead ∧ Cont eta gamma sourceRead ∧
                        Cont gamma application gammaRead ∧
                          Cont application replay operationRead ∧
                            Cont operationRead provenance supportRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation
    operationProvenanceSupport supportPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed operationReadUnary provenanceUnary operationProvenanceSupport
  exact
    ⟨etaUnary, gammaUnary, applicationUnary, replayUnary, provenanceUnary, sourceReadUnary,
      gammaReadUnary, operationReadUnary, supportReadUnary, etaGammaSource,
      gammaApplicationRead, applicationReplayOperation, operationProvenanceSupport,
      provenancePkg, supportPkg⟩

theorem ZetaContinuationApplicationClassifierStabilityObligation [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      gammaRead operationRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame etaRead eta →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont etaRead operationRead classifierRead →
              PkgSig bundle classifierRead pkg →
                UnaryHistory etaRead ∧ UnaryHistory eta ∧ UnaryHistory gamma ∧
                  UnaryHistory application ∧ UnaryHistory gammaRead ∧
                    UnaryHistory operationRead ∧ UnaryHistory classifierRead ∧
                      Cont eta functional application ∧ Cont gamma application gammaRead ∧
                        Cont application replay operationRead ∧
                          Cont etaRead operationRead classifierRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg Cont UnaryHistory
  intro carrier sameEtaRead gammaApplicationRead applicationReplayOperation
    etaReadOperationClassifier classifierPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_transport etaUnary (hsame_symm sameEtaRead)
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed etaReadUnary operationReadUnary etaReadOperationClassifier
  exact
    ⟨etaReadUnary, etaUnary, gammaUnary, applicationUnary, gammaReadUnary,
      operationReadUnary, classifierReadUnary, etaFunctionalApplication, gammaApplicationRead,
      applicationReplayOperation, etaReadOperationClassifier, provenancePkg, classifierPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
