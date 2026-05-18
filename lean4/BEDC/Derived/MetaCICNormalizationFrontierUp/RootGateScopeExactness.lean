import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootGateScopeExactness [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRoute gateScope retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint endpointRead →
          Cont obstruction replay obstructionRoute →
            Cont candidateRead endpointRead gateScope →
              Cont gateScope obstructionRoute retainedRead →
                PkgSig bundle retainedRead pkg →
                  UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                    UnaryHistory obstructionRoute ∧ UnaryHistory gateScope ∧
                      UnaryHistory retainedRead ∧ Cont candidate closedCandidate candidateRead ∧
                        Cont finished endpoint endpointRead ∧ Cont obstruction replay
                          obstructionRoute ∧ Cont candidateRead endpointRead gateScope ∧
                            Cont gateScope obstructionRoute retainedRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle retainedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRoute
    candidateEndpointGate gateObstructionRetained retainedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionRouteUnary : UnaryHistory obstructionRoute :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRoute
  have gateScopeUnary : UnaryHistory gateScope :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointGate
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed gateScopeUnary obstructionRouteUnary gateObstructionRetained
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionRouteUnary, gateScopeUnary,
      retainedReadUnary, candidateClosedRead, finishedEndpointRead, obstructionReplayRoute,
      candidateEndpointGate, gateObstructionRetained, provenancePkg, retainedPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
