import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_replay_nonescape [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name rootReplay
      replayOut boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont replay provenance rootReplay →
        Cont rootReplay name replayOut →
          Cont replayOut boundary provenance →
            PkgSig bundle replayOut pkg →
              UnaryHistory replay ∧ UnaryHistory rootReplay ∧ UnaryHistory replayOut ∧
                UnaryHistory provenance ∧ Cont replay provenance rootReplay ∧
                  Cont rootReplay name replayOut ∧ Cont replayOut boundary provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle replayOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier replayProvenanceRoot rootNameReplayOut replayOutBoundaryProvenance
    replayOutPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    _applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have rootReplayUnary : UnaryHistory rootReplay :=
    unary_cont_closed replayUnary provenanceUnary replayProvenanceRoot
  have replayOutUnary : UnaryHistory replayOut :=
    unary_cont_closed rootReplayUnary nameUnary rootNameReplayOut
  exact
    ⟨replayUnary, rootReplayUnary, replayOutUnary, provenanceUnary, replayProvenanceRoot,
      rootNameReplayOut, replayOutBoundaryProvenance, provenancePkg, replayOutPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
