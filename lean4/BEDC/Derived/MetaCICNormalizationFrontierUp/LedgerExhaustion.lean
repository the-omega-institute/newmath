import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_ledger_exhaustion [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont endpointRead provenance ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory endpointRead ∧ UnaryHistory ledgerRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint finishedRead ∧ Cont endpoint replay endpointRead ∧
                        Cont endpointRead provenance ledgerRead ∧
                          hsame transport (append candidate finished) ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    endpointProvenanceLedger ledgerPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed endpointReadUnary provenanceUnary endpointProvenanceLedger
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, ledgerReadUnary,
      candidateClosedRead, finishedEndpointRead, endpointReplayRead, endpointProvenanceLedger,
      transportSameCandidateFinished, provenancePkg, ledgerPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
