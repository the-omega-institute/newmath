import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_candidate_endpoint_coherence
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead coherenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont candidateRead endpointRead coherenceRead ->
            PkgSig bundle coherenceRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory coherenceRead ∧ hsame transport (append candidate finished) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle coherenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidateEndpointCoherence
    coherencePkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have coherenceReadUnary : UnaryHistory coherenceRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointCoherence
  exact
    ⟨candidateReadUnary, endpointReadUnary, coherenceReadUnary,
      transportSameCandidateFinished, provenancePkg, coherencePkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
