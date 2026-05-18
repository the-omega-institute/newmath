import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_carrier_rows [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧ UnaryHistory finished ∧
        UnaryHistory endpoint ∧ UnaryHistory obstruction ∧ UnaryHistory transport ∧
          UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localRow ∧
            Cont candidate closedCandidate localRow ∧ Cont finished endpoint replay ∧
              Cont endpoint replay provenance ∧ hsame transport (append candidate finished) ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, provenanceUnary, localRowUnary,
    candidateClosedLocal, finishedEndpointReplay, endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  exact
    ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary, obstructionUnary,
      transportUnary, replayUnary, provenanceUnary, localRowUnary, candidateClosedLocal,
      finishedEndpointReplay, endpointReplayProvenance, transportSameCandidateFinished,
      provenancePkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
