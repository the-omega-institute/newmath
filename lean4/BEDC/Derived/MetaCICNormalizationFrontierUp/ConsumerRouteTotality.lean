import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consumer_route_totality [AskSetup]
    [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead replay routeRead ->
            Cont finishedRead replay routeRead ->
              PkgSig bundle routeRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory routeRead ∧ Cont candidate closedCandidate candidateRead ∧
                    Cont finished endpoint finishedRead ∧
                      (hsame routeRead candidateRead ∨ hsame routeRead finishedRead ∨
                        hsame routeRead routeRead) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead candidateReplayRoute
    _finishedReplayRoute routePkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayRoute
  exact
    ⟨candidateReadUnary, finishedReadUnary, routeReadUnary, candidateClosedRead,
      finishedEndpointRead, Or.inr (Or.inr (hsame_refl routeRead)), provenancePkg,
      routePkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
