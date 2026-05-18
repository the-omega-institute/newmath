import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_subject_obstruction_preservation
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead obstructionRead retainedCandidate retainedFinished : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction replay obstructionRead ->
            Cont candidateRead obstructionRead retainedCandidate ->
              Cont finishedRead obstructionRead retainedFinished ->
                PkgSig bundle retainedCandidate pkg ->
                  PkgSig bundle retainedFinished pkg ->
                    UnaryHistory obstruction ∧ UnaryHistory obstructionRead ∧
                      UnaryHistory retainedCandidate ∧ UnaryHistory retainedFinished ∧
                        Cont obstruction replay obstructionRead ∧
                          Cont candidateRead obstructionRead retainedCandidate ∧
                            Cont finishedRead obstructionRead retainedFinished ∧
                              hsame transport (append candidate finished) ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle retainedCandidate pkg ∧
                                    PkgSig bundle retainedFinished pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRead
    candidateObstructionRetained finishedObstructionRetained retainedCandidatePkg
    retainedFinishedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRead
  have retainedCandidateUnary : UnaryHistory retainedCandidate :=
    unary_cont_closed candidateReadUnary obstructionReadUnary candidateObstructionRetained
  have retainedFinishedUnary : UnaryHistory retainedFinished :=
    unary_cont_closed finishedReadUnary obstructionReadUnary finishedObstructionRetained
  exact
    ⟨obstructionUnary, obstructionReadUnary, retainedCandidateUnary, retainedFinishedUnary,
      obstructionReplayRead, candidateObstructionRetained, finishedObstructionRetained,
      transportSameCandidateFinished, provenancePkg, retainedCandidatePkg, retainedFinishedPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
