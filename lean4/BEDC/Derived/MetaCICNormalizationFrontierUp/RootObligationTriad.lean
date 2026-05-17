import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_obligation_triad [AskSetup]
    [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRoute rootRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction replay obstructionRoute ->
            Cont candidateRead obstructionRoute rootRoute ->
              PkgSig bundle rootRoute pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory obstructionRoute ∧ UnaryHistory rootRoute ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint finishedRead ∧
                        Cont obstruction replay obstructionRoute ∧
                          Cont candidateRead obstructionRoute rootRoute ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRoute
    candidateObstructionRoot rootPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionRouteUnary : UnaryHistory obstructionRoute :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRoute
  have rootRouteUnary : UnaryHistory rootRoute :=
    unary_cont_closed candidateReadUnary obstructionRouteUnary candidateObstructionRoot
  exact
    ⟨candidateReadUnary, finishedReadUnary, obstructionRouteUnary, rootRouteUnary,
      candidateClosedRead, finishedEndpointRead, obstructionReplayRoute,
      candidateObstructionRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
