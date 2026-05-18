import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_substitution_stability [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead obstructionRead endpointRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction transport obstructionRead ->
            Cont endpoint replay endpointRead ->
              Cont endpointRead localRow substitutionRead ->
                PkgSig bundle substitutionRead pkg ->
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory obstructionRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory substitutionRead ∧ hsame transport (append candidate finished) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle substitutionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    endpointReplayRead endpointLocalSubstitution substitutionPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalSubstitution
  exact
    ⟨candidateReadUnary, finishedReadUnary, obstructionReadUnary, endpointReadUnary,
      substitutionReadUnary, transportSameCandidateFinished, provenancePkg, substitutionPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
