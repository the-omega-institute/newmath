import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead candidatePublic endpointPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont candidateRead replay candidatePublic →
          Cont finished endpoint endpointRead →
            Cont endpointRead replay endpointPublic →
              PkgSig bundle candidatePublic pkg →
                PkgSig bundle endpointPublic pkg →
                  UnaryHistory candidateRead ∧ UnaryHistory candidatePublic ∧
                    UnaryHistory endpointRead ∧ UnaryHistory endpointPublic ∧
                      PkgSig bundle candidatePublic pkg ∧
                        PkgSig bundle endpointPublic pkg ∧ hsame obstruction obstruction := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier candidateClosedRead candidateReplayPublic finishedEndpointRead
    endpointReplayPublic candidatePkg endpointPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have candidatePublicUnary : UnaryHistory candidatePublic :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayPublic
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointPublicUnary : UnaryHistory endpointPublic :=
    unary_cont_closed endpointReadUnary replayUnary endpointReplayPublic
  exact
    ⟨candidateReadUnary, candidatePublicUnary, endpointReadUnary, endpointPublicUnary,
      candidatePkg, endpointPkg, hsame_refl obstruction⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
