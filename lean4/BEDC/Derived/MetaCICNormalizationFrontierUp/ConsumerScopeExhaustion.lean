import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consumer_scope_exhaustion
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead obstructionRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont obstruction transport obstructionRead ->
              Cont candidateRead finishedRead consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory obstructionRead ∧
                      UnaryHistory consumerRead ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidateRead ∨ hsame row finishedRead ∨
                              hsame row endpointRead ∨ hsame row obstructionRead ∨
                                hsame row consumerRead)
                          (fun row : BHist =>
                            PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    obstructionTransportRead candidateFinishedConsumer consumerPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
            hsame row obstructionRead ∨ hsame row consumerRead)
        (fun row : BHist => PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨consumerPkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, obstructionReadUnary,
      consumerReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
