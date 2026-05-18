import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootNormalizationGateExhaustion [AskSetup]
    [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead obstructionRead normalGate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont candidateRead endpointRead normalGate ->
              PkgSig bundle normalGate pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory normalGate ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint endpointRead ∧
                        Cont obstruction transport obstructionRead ∧
                          Cont candidateRead endpointRead normalGate ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle normalGate pkg ∧
                              hsame transport (append candidate finished) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    candidateEndpointGate normalGatePkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have normalGateUnary : UnaryHistory normalGate :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointGate
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionReadUnary, normalGateUnary,
      candidateClosedRead, finishedEndpointRead, obstructionTransportRead,
      candidateEndpointGate, provenancePkg, normalGatePkg, transportSameCandidateFinished⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
