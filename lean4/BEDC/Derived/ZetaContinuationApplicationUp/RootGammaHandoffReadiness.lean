import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_gamma_handoff_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name gammaRead
      gammaReplay gammaBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRead →
        Cont gammaRead replay gammaReplay →
          Cont gammaReplay provenance gammaBoundary →
            PkgSig bundle gammaBoundary pkg →
              UnaryHistory gamma ∧ UnaryHistory application ∧ UnaryHistory replay ∧
                UnaryHistory provenance ∧ UnaryHistory gammaRead ∧
                  UnaryHistory gammaReplay ∧ UnaryHistory gammaBoundary ∧
                    Cont gamma application gammaRead ∧ Cont gammaRead replay gammaReplay ∧
                      Cont gammaReplay provenance gammaBoundary ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle gammaBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gammaApplicationRead gammaReadReplay gammaReplayProvenance gammaBoundaryPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have gammaReplayUnary : UnaryHistory gammaReplay :=
    unary_cont_closed gammaReadUnary replayUnary gammaReadReplay
  have gammaBoundaryUnary : UnaryHistory gammaBoundary :=
    unary_cont_closed gammaReplayUnary provenanceUnary gammaReplayProvenance
  exact
    ⟨gammaUnary, applicationUnary, replayUnary, provenanceUnary, gammaReadUnary,
      gammaReplayUnary, gammaBoundaryUnary, gammaApplicationRead, gammaReadReplay,
      gammaReplayProvenance, provenancePkg, gammaBoundaryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
