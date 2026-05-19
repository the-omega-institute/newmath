import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierVisibleObstructionAdmission
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead obstructionRoute visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction replay obstructionRoute ->
            Cont endpointRead obstructionRoute visibleRead ->
              PkgSig bundle visibleRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory obstructionRoute ∧ UnaryHistory visibleRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint endpointRead ∧
                        Cont obstruction replay obstructionRoute ∧
                          Cont endpointRead obstructionRoute visibleRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle visibleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRoute
    endpointObstructionVisible visiblePkg
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
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed endpointReadUnary obstructionRouteUnary endpointObstructionVisible
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionRouteUnary, visibleReadUnary,
      candidateClosedRead, finishedEndpointRead, obstructionReplayRoute,
      endpointObstructionVisible, provenancePkg, visiblePkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
