import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_consumer_nonescape
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow rootRead candidateRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont candidateRead endpointRead rootRead ->
            Cont rootRead replay publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory rootRead ∧ UnaryHistory publicRead ∧
                  PkgSig bundle publicRead pkg ∧
                    (Cont publicRead (BHist.e0 obstruction) rootRead -> False) ∧
                      (Cont publicRead (BHist.e1 obstruction) rootRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead candidateEndpointRoot
    rootReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointRoot
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rootUnary replayUnary rootReplayPublic
  exact
    ⟨rootUnary, publicUnary, publicPkg,
      (cont_mutual_extension_right_tail_absurd.left rootReplayPublic),
      (cont_mutual_extension_right_tail_absurd.right rootReplayPublic)⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
