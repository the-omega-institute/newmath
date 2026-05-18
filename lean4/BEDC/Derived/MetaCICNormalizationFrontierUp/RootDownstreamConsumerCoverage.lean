import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootDownstreamConsumerCoverage [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont endpoint replay endpointRead →
          Cont obstruction transport obstructionRead →
            Cont candidateRead endpointRead downstreamRead →
              PkgSig bundle downstreamRead pkg →
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory downstreamRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont endpoint replay endpointRead ∧
                        Cont obstruction transport obstructionRead ∧
                          Cont candidateRead endpointRead downstreamRead ∧
                            hsame transport (append candidate finished) ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle hsame UnaryHistory
  intro carrier candidateClosedRead endpointReplayRead obstructionTransportRead
    candidateEndpointDownstream downstreamPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointDownstream
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionReadUnary, downstreamReadUnary,
      candidateClosedRead, endpointReplayRead, obstructionTransportRead,
      candidateEndpointDownstream, transportSameCandidateFinished, provenancePkg,
      downstreamPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
