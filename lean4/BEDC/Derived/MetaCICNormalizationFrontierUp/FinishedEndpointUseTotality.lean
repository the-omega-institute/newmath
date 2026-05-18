import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_finished_endpoint_use_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      finishedRead endpointRead supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow supportRead ->
            PkgSig bundle supportRead pkg ->
              UnaryHistory finished ∧ UnaryHistory endpoint ∧ UnaryHistory finishedRead ∧
                UnaryHistory endpointRead ∧ UnaryHistory supportRead ∧
                  Cont finished endpoint finishedRead ∧
                    Cont finishedRead replay endpointRead ∧
                      Cont endpointRead localRow supportRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier finishedEndpointRead finishedReplayEndpoint endpointLocalSupport supportPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalSupport
  exact
    ⟨finishedUnary, endpointUnary, finishedReadUnary, endpointReadUnary, supportReadUnary,
      finishedEndpointRead, finishedReplayEndpoint, endpointLocalSupport, provenancePkg,
      supportPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
