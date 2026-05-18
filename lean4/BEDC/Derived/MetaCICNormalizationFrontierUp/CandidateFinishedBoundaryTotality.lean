import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_candidate_finished_boundary_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead finishedRead boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                UnaryHistory boundaryRead ∧ Cont candidate closedCandidate candidateRead ∧
                  Cont finished endpoint finishedRead ∧
                    Cont candidateRead finishedRead boundaryRead ∧
                      (hsame transport (append candidate finished) ∨
                        hsame transport (append candidateRead finishedRead)) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier candidateClosedRead finishedEndpointRead candidateFinishedBoundary boundaryPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedBoundary
  exact
    ⟨candidateReadUnary, finishedReadUnary, boundaryReadUnary, candidateClosedRead,
      finishedEndpointRead, candidateFinishedBoundary, Or.inl transportSameCandidateFinished,
      provenancePkg, boundaryPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
