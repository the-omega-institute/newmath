import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consistency_consumer_factorization
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead candidatePublic finishedPublic consistencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont candidateRead replay candidatePublic ->
              Cont finishedRead replay finishedPublic ->
                Cont candidatePublic endpointRead consistencyRead ->
                  PkgSig bundle consistencyRead pkg ->
                    UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                      UnaryHistory endpointRead ∧ UnaryHistory candidatePublic ∧
                        UnaryHistory finishedPublic ∧ UnaryHistory consistencyRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row candidatePublic ∨ hsame row finishedPublic ∨
                                hsame row endpointRead ∨ hsame row obstruction ∨
                                  hsame row consistencyRead)
                            (fun row : BHist =>
                              PkgSig bundle consistencyRead pkg ∧ hsame row consistencyRead)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    candidateReplayPublic finishedReplayPublic candidateEndpointConsistency consistencyPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have candidatePublicUnary : UnaryHistory candidatePublic :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayPublic
  have finishedPublicUnary : UnaryHistory finishedPublic :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayPublic
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed candidatePublicUnary endpointReadUnary candidateEndpointConsistency
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consistencyRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidatePublic ∨ hsame row finishedPublic ∨ hsame row endpointRead ∨
            hsame row obstruction ∨ hsame row consistencyRead)
        (fun row : BHist => PkgSig bundle consistencyRead pkg ∧ hsame row consistencyRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consistencyRead ⟨hsame_refl consistencyRead, consistencyUnary⟩
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
        exact ⟨consistencyPkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, candidatePublicUnary,
      finishedPublicUnary, consistencyUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
