import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_carrier_admission_route
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont endpoint replay endpointRead →
            Cont endpointRead localRow publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧
                  UnaryHistory finished ∧ UnaryHistory endpoint ∧ UnaryHistory obstruction ∧
                    UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                      UnaryHistory endpointRead ∧ UnaryHistory publicRead ∧
                        Cont candidate closedCandidate candidateRead ∧
                          Cont finished endpoint finishedRead ∧
                            Cont endpoint replay endpointRead ∧
                              Cont endpointRead localRow publicRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    endpointLocalPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalPublic
  exact
    ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary, obstructionUnary,
      candidateReadUnary, finishedReadUnary, endpointReadUnary, publicReadUnary,
      candidateClosedRead, finishedEndpointRead, endpointReplayRead, endpointLocalPublic,
      provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
