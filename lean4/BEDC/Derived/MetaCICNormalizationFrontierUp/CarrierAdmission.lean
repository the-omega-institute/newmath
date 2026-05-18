import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrierAdmission [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead closedNormalRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont endpointRead provenance closedNormalRead ->
              Cont localRow closedNormalRead structuralRead ->
                PkgSig bundle structuralRead pkg ->
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory closedNormalRead ∧
                      UnaryHistory structuralRead ∧
                        Cont candidate closedCandidate candidateRead ∧
                          Cont finished endpoint finishedRead ∧
                            Cont endpoint replay endpointRead ∧
                              Cont endpointRead provenance closedNormalRead ∧
                                Cont localRow closedNormalRead structuralRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle structuralRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    endpointProvenanceClosed localClosedStructural structuralPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have closedNormalReadUnary : UnaryHistory closedNormalRead :=
    unary_cont_closed endpointReadUnary provenanceUnary endpointProvenanceClosed
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed localRowUnary closedNormalReadUnary localClosedStructural
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, closedNormalReadUnary,
      structuralReadUnary, candidateClosedRead, finishedEndpointRead, endpointReplayRead,
      endpointProvenanceClosed, localClosedStructural, provenancePkg, structuralPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
