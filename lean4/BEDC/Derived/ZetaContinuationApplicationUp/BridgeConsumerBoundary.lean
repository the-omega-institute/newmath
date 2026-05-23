import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_bridge_consumer_boundary [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      gammaRead operationRead zetaRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRead →
        Cont application replay operationRead →
          Cont eta gamma zetaRead →
            Cont operationRead provenance bridgeRead →
              PkgSig bundle bridgeRead pkg →
                UnaryHistory gammaRead ∧ UnaryHistory operationRead ∧
                  UnaryHistory zetaRead ∧ UnaryHistory bridgeRead ∧
                    Cont gamma application gammaRead ∧
                      Cont application replay operationRead ∧ Cont eta gamma zetaRead ∧
                        Cont operationRead provenance bridgeRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gammaApplicationRead applicationReplayRead etaGammaRead operationProvenanceRead
    bridgePkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRead
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaRead
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed operationReadUnary provenanceUnary operationProvenanceRead
  exact
    ⟨gammaReadUnary,
      operationReadUnary,
      zetaReadUnary,
      bridgeReadUnary,
      gammaApplicationRead,
      applicationReplayRead,
      etaGammaRead,
      operationProvenanceRead,
      provenancePkg,
      bridgePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
