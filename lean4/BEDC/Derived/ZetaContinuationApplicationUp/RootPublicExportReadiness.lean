import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_public_export_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      gammaRead operationRead ledgerRead publicRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont provenance name ledgerRead →
              Cont operationRead ledgerRead publicRead →
                Cont transport replay rootRead →
                  PkgSig bundle publicRead pkg →
                    PkgSig bundle rootRead pkg →
                      UnaryHistory eta ∧ UnaryHistory functional ∧ UnaryHistory gamma ∧
                        UnaryHistory application ∧ UnaryHistory transport ∧
                          UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                            UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                              UnaryHistory operationRead ∧ UnaryHistory ledgerRead ∧
                                UnaryHistory publicRead ∧ UnaryHistory rootRead ∧
                                  Cont eta functional application ∧
                                    Cont gamma application replay ∧
                                      Cont transport replay provenance ∧
                                        Cont eta gamma sourceRead ∧
                                          Cont gamma application gammaRead ∧
                                            Cont application replay operationRead ∧
                                              Cont provenance name ledgerRead ∧
                                                Cont operationRead ledgerRead publicRead ∧
                                                  Cont transport replay rootRead ∧
                                                    PkgSig bundle provenance pkg ∧
                                                      PkgSig bundle name pkg ∧
                                                        PkgSig bundle publicRead pkg ∧
                                                          PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation
    provenanceNameLedger operationLedgerPublic transportReplayRoot publicPkg rootPkg
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, transportUnary, replayUnary, provenanceUnary, nameUnary,
    transportReplayProvenance, etaFunctionalApplication, gammaApplicationReplay, provenancePkg,
    namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameLedger
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed operationReadUnary ledgerReadUnary operationLedgerPublic
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed transportUnary replayUnary transportReplayRoot
  exact
    ⟨etaUnary, functionalUnary, gammaUnary, applicationUnary, transportUnary, replayUnary,
      provenanceUnary, nameUnary, sourceReadUnary, gammaReadUnary, operationReadUnary,
      ledgerReadUnary, publicReadUnary, rootReadUnary, etaFunctionalApplication,
      gammaApplicationReplay, transportReplayProvenance, etaGammaSource, gammaApplicationRead,
      applicationReplayOperation, provenanceNameLedger, operationLedgerPublic,
      transportReplayRoot, provenancePkg, namePkg, publicPkg, rootPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
