import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_public_nonescape_package [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name publicRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      UnaryHistory publicRead →
        Cont application provenance consumer →
          Cont publicRead consumer provenance →
            PkgSig bundle consumer pkg →
              UnaryHistory application ∧ UnaryHistory provenance ∧ UnaryHistory consumer ∧
                hsame consumer (append application provenance) ∧
                  hsame provenance (append publicRead consumer) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _publicReadUnary applicationProvenanceConsumer publicConsumerProvenance
    consumerPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed applicationUnary provenanceUnary applicationProvenanceConsumer
  exact
    ⟨applicationUnary, provenanceUnary, consumerUnary, applicationProvenanceConsumer,
      publicConsumerProvenance, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
