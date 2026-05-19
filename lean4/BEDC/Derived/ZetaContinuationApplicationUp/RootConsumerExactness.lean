import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_consumer_exactness [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      gammaRead operationRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont provenance name ledgerRead →
              Cont operationRead ledgerRead publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                    UnaryHistory operationRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory publicRead ∧ Cont eta gamma sourceRead ∧
                        Cont gamma application gammaRead ∧
                          Cont application replay operationRead ∧
                            Cont provenance name ledgerRead ∧
                              Cont operationRead ledgerRead publicRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation
    provenanceNameLedger operationLedgerPublic publicPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
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
  exact
    ⟨sourceReadUnary, gammaReadUnary, operationReadUnary, ledgerReadUnary, publicReadUnary,
      etaGammaSource, gammaApplicationRead, applicationReplayOperation, provenanceNameLedger,
      operationLedgerPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
