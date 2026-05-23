import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_candidate_confluence_budget
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead boundaryRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead finishedRead boundaryRead ->
            Cont boundaryRead obstruction confluenceRead ->
              PkgSig bundle confluenceRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory confluenceRead ∧
                    Cont candidateRead finishedRead boundaryRead ∧
                      Cont boundaryRead obstruction confluenceRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle confluenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier candidateClosedRead finishedEndpointRead candidateFinishedBoundary
    boundaryObstructionConfluence confluencePkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedBoundary
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed boundaryReadUnary obstructionUnary boundaryObstructionConfluence
  exact
    ⟨candidateReadUnary, finishedReadUnary, boundaryReadUnary, confluenceReadUnary,
      candidateFinishedBoundary, boundaryObstructionConfluence, provenancePkg, confluencePkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
