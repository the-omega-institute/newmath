import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_closed_candidate_readback_exhaustion
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead supportRead closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont candidateRead replay supportRead →
          Cont supportRead localRow closedRead →
            PkgSig bundle closedRead pkg →
              UnaryHistory candidateRead ∧ UnaryHistory supportRead ∧
                UnaryHistory closedRead ∧ Cont candidate closedCandidate candidateRead ∧
                  Cont candidateRead replay supportRead ∧
                    Cont supportRead localRow closedRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle closedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead candidateReplaySupport supportLocalClosed closedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplaySupport
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed supportReadUnary localRowUnary supportLocalClosed
  exact
    ⟨candidateReadUnary, supportReadUnary, closedReadUnary, candidateClosedRead,
      candidateReplaySupport, supportLocalClosed, provenancePkg, closedPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
