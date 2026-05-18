import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootObstructionStability [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRoute retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint endpointRead →
          Cont obstruction replay obstructionRoute →
            Cont candidateRead obstructionRoute retainedRead →
              PkgSig bundle retainedRead pkg →
                UnaryHistory obstruction ∧ UnaryHistory obstructionRoute ∧
                  UnaryHistory retainedRead ∧ Cont obstruction replay obstructionRoute ∧
                    Cont candidateRead obstructionRoute retainedRead ∧
                      hsame transport (append candidate finished) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle retainedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle hsame UnaryHistory
  intro carrier candidateClosedRead _finishedEndpointRead obstructionReplayRoute
    candidateObstructionRetained retainedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have obstructionRouteUnary : UnaryHistory obstructionRoute :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRoute
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed candidateReadUnary obstructionRouteUnary candidateObstructionRetained
  exact
    ⟨obstructionUnary, obstructionRouteUnary, retainedReadUnary, obstructionReplayRoute,
      candidateObstructionRetained, transportSameCandidateFinished, provenancePkg,
      retainedPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
