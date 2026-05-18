import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierVisibleObstruction_route_factorization
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead obstructionRead visibleRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont obstructionRead replay visibleRead ->
              Cont candidateRead endpointRead publicRead ->
                PkgSig bundle visibleRead pkg ->
                  PkgSig bundle publicRead pkg ->
                    UnaryHistory obstructionRead ∧ UnaryHistory visibleRead ∧
                      UnaryHistory publicRead ∧ Cont obstructionRead replay visibleRead ∧
                        Cont candidateRead endpointRead publicRead ∧
                          PkgSig bundle visibleRead pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    obstructionReplayVisible candidateEndpointPublic visiblePkg publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayVisible
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointPublic
  exact
    ⟨obstructionReadUnary, visibleReadUnary, publicReadUnary, obstructionReplayVisible,
      candidateEndpointPublic, visiblePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
