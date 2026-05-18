import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_candidate_gate_projection
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont candidateRead replay publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory candidateRead ∧ UnaryHistory publicRead ∧
              Cont candidate closedCandidate candidateRead ∧
                Cont candidateRead replay publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead candidateReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayPublic
  exact
    ⟨candidateReadUnary, publicReadUnary, candidateClosedRead, candidateReplayPublic,
      provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
