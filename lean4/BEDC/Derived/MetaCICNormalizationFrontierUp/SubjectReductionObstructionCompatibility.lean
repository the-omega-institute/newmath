import BEDC.Derived.MetaCICNormalizationFrontierUp.SubjectObstructionPreservation

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierSubjectReductionObstructionCompatibility
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead obstructionRead retainedCandidate retainedFinished
      subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont obstruction replay obstructionRead →
            Cont candidateRead obstructionRead retainedCandidate →
              Cont finishedRead obstructionRead retainedFinished →
                Cont retainedCandidate retainedFinished subjectRead →
                  PkgSig bundle retainedCandidate pkg →
                    PkgSig bundle retainedFinished pkg →
                      PkgSig bundle subjectRead pkg →
                        UnaryHistory obstruction ∧ UnaryHistory obstructionRead ∧
                          UnaryHistory retainedCandidate ∧ UnaryHistory retainedFinished ∧
                            UnaryHistory subjectRead ∧ Cont obstruction replay obstructionRead ∧
                              Cont candidateRead obstructionRead retainedCandidate ∧
                                Cont finishedRead obstructionRead retainedFinished ∧
                                  Cont retainedCandidate retainedFinished subjectRead ∧
                                    hsame transport (append candidate finished) ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle subjectRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRead
    candidateObstructionRetained finishedObstructionRetained retainedSubject
    retainedCandidatePkg retainedFinishedPkg subjectPkg
  have preserved :=
    MetaCICNormalizationFrontierCarrier_subject_obstruction_preservation
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (obstructionRead := obstructionRead) (retainedCandidate := retainedCandidate)
      (retainedFinished := retainedFinished) (bundle := bundle) (pkg := pkg)
      carrier candidateClosedRead finishedEndpointRead obstructionReplayRead
      candidateObstructionRetained finishedObstructionRetained retainedCandidatePkg
      retainedFinishedPkg
  obtain ⟨obstructionUnary, obstructionReadUnary, retainedCandidateUnary,
    retainedFinishedUnary, obstructionReplay, candidateRetained, finishedRetained,
    transportSame, provenancePkg, _retainedCandidatePkg, _retainedFinishedPkg⟩ := preserved
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed retainedCandidateUnary retainedFinishedUnary retainedSubject
  exact
    ⟨obstructionUnary, obstructionReadUnary, retainedCandidateUnary, retainedFinishedUnary,
      subjectUnary, obstructionReplay, candidateRetained, finishedRetained, retainedSubject,
      transportSame, provenancePkg, subjectPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
