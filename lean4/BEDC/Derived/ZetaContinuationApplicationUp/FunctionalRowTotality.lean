import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_functional_row_totality [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name functionalRead
      gammaRead operationRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont functional gamma functionalRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont operationRead provenance publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory functional ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
                  UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory functionalRead ∧
                    UnaryHistory gammaRead ∧ UnaryHistory operationRead ∧
                      UnaryHistory publicRead ∧ Cont functional gamma functionalRead ∧
                        Cont gamma application gammaRead ∧
                          Cont application replay operationRead ∧
                            Cont operationRead provenance publicRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier functionalGammaRead gammaApplicationRead applicationReplayOperation
    operationProvenancePublic publicPkg
  obtain ⟨_etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed operationReadUnary provenanceUnary operationProvenancePublic
  exact
    ⟨functionalUnary, gammaUnary, applicationUnary, replayUnary, provenanceUnary,
      functionalReadUnary, gammaReadUnary, operationReadUnary, publicReadUnary,
      functionalGammaRead, gammaApplicationRead, applicationReplayOperation,
      operationProvenancePublic, provenancePkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
