import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_closed_normal_consumer_route
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow finishedRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory finished ∧ UnaryHistory endpoint ∧ UnaryHistory finishedRead ∧
                UnaryHistory endpointRead ∧ UnaryHistory publicRead ∧
                  Cont finished endpoint finishedRead ∧
                    Cont finishedRead replay endpointRead ∧
                      Cont endpointRead localRow publicRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier finishedEndpointRead finishedReplayRead endpointLocalRead publicPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalRead
  exact
    ⟨finishedUnary, endpointUnary, finishedReadUnary, endpointReadUnary, publicReadUnary,
      finishedEndpointRead, finishedReplayRead, endpointLocalRead, provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
