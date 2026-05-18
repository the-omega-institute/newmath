import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_formal_target_classifier_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRead endpointRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction transport obstructionRead ->
            Cont endpoint replay endpointRead ->
              Cont candidateRead endpointRead classifierRead ->
                PkgSig bundle classifierRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row finishedRead ∨
                          hsame row obstructionRead ∨ hsame row endpointRead ∨
                            hsame row classifierRead)
                      (fun row : BHist =>
                        PkgSig bundle classifierRead pkg ∧ hsame row classifierRead)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                      UnaryHistory obstructionRead ∧ UnaryHistory endpointRead ∧
                        UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    endpointReplayRead candidateEndpointClassifier classifierPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointClassifier
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row finishedRead ∨
            hsame row obstructionRead ∨ hsame row endpointRead ∨
              hsame row classifierRead)
        (fun row : BHist => PkgSig bundle classifierRead pkg ∧ hsame row classifierRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro classifierRead ⟨hsame_refl classifierRead, classifierReadUnary⟩
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
        exact ⟨classifierPkg, source.left⟩
    }
  exact
    ⟨cert, candidateReadUnary, finishedReadUnary, obstructionReadUnary, endpointReadUnary,
      classifierReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
