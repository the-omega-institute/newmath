import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootHandoffScope [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont endpoint replay endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont endpointRead localRow handoffRead ->
              PkgSig bundle handoffRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory handoffRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont endpoint replay endpointRead ∧
                        Cont obstruction transport obstructionRead ∧
                          Cont endpointRead localRow handoffRead ∧
                            hsame transport (append candidate finished) ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier candidateClosedRead endpointReplayRead obstructionTransportRead
    endpointLocalHandoff handoffPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalHandoff
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionReadUnary, handoffReadUnary,
      candidateClosedRead, endpointReplayRead, obstructionTransportRead, endpointLocalHandoff,
      transportSameCandidateFinished, provenancePkg, handoffPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
