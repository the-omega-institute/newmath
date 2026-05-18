import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_formal_target_carrier_coverage
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRead endpointRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction transport obstructionRead ->
            Cont endpoint replay endpointRead ->
              Cont candidateRead endpointRead handoffRead ->
                PkgSig bundle handoffRead pkg ->
                  UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧
                    UnaryHistory finished ∧ UnaryHistory endpoint ∧
                      UnaryHistory obstruction ∧ UnaryHistory transport ∧
                        UnaryHistory replay ∧ UnaryHistory provenance ∧
                          UnaryHistory localRow ∧ UnaryHistory candidateRead ∧
                            UnaryHistory finishedRead ∧ UnaryHistory obstructionRead ∧
                              UnaryHistory endpointRead ∧ UnaryHistory handoffRead ∧
                                Cont candidate closedCandidate candidateRead ∧
                                  Cont finished endpoint finishedRead ∧
                                    Cont obstruction transport obstructionRead ∧
                                      Cont endpoint replay endpointRead ∧
                                        Cont candidateRead endpointRead handoffRead ∧
                                          hsame transport (append candidate finished) ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    endpointReplayRead candidateEndpointHandoff handoffPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointHandoff
  exact
    ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary, obstructionUnary,
      transportUnary, replayUnary, provenanceUnary, localRowUnary, candidateReadUnary,
      finishedReadUnary, obstructionReadUnary, endpointReadUnary, handoffReadUnary,
      candidateClosedRead, finishedEndpointRead, obstructionTransportRead, endpointReplayRead,
      candidateEndpointHandoff, transportSameCandidateFinished, provenancePkg, handoffPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
