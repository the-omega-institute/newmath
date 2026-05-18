import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_carrier_rows [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧
                UnaryHistory finished ∧ UnaryHistory endpoint ∧ UnaryHistory obstruction ∧
                  UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
                    UnaryHistory localRow ∧ UnaryHistory candidateRead ∧
                      UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
                        Cont candidate closedCandidate candidateRead ∧
                          Cont finished endpoint finishedRead ∧
                            Cont endpoint replay endpointRead ∧
                              hsame transport (append candidate finished) ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead endpointReadPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  exact
    ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary, obstructionUnary,
      transportUnary, replayUnary, provenanceUnary, localRowUnary, candidateReadUnary,
      finishedReadUnary, endpointReadUnary, candidateClosedRead, finishedEndpointRead,
      endpointReplayRead, transportSameCandidateFinished, provenancePkg, endpointReadPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
