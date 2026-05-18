import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierFormalTargetLedgerNonescape [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont localRow endpointRead ledgerRead ->
              PkgSig bundle endpointRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory ledgerRead ∧
                      Cont candidate closedCandidate candidateRead ∧
                        Cont finished endpoint finishedRead ∧ Cont endpoint replay endpointRead ∧
                          Cont localRow endpointRead ledgerRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg ∧
                              PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead localEndpointLedger
    endpointReadPkg ledgerReadPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed localRowUnary endpointReadUnary localEndpointLedger
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, ledgerReadUnary,
      candidateClosedRead, finishedEndpointRead, endpointReplayRead, localEndpointLedger,
      provenancePkg, endpointReadPkg, ledgerReadPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
