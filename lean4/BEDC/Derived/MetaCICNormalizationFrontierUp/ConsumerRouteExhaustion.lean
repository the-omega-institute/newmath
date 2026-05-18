import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consumer_route_exhaustion
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont endpoint replay endpointRead →
            Cont endpointRead localRow consumerRead →
              PkgSig bundle consumerRead pkg →
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory endpointRead ∧ UnaryHistory consumerRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint finishedRead ∧
                        Cont endpoint replay endpointRead ∧
                          Cont endpointRead localRow consumerRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    endpointLocalConsumer consumerPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalConsumer
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, consumerReadUnary,
      candidateClosedRead, finishedEndpointRead, endpointReplayRead, endpointLocalConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
