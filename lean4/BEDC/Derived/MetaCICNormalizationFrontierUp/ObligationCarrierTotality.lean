import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obligation_carrier_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead closedNormalRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont endpoint replay endpointRead ->
            Cont endpointRead provenance closedNormalRead ->
              Cont localRow closedNormalRead structuralRead ->
                PkgSig bundle structuralRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        MetaCICNormalizationFrontierCarrier candidate closedCandidate finished
                          endpoint obstruction transport replay provenance localRow bundle pkg ∧
                          hsame row localRow)
                      (fun row : BHist =>
                        hsame row localRow ∧ UnaryHistory row ∧
                          Cont candidate closedCandidate candidateRead ∧
                            Cont finished endpoint finishedRead ∧
                              Cont endpoint replay endpointRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle structuralRead pkg ∧
                          hsame row localRow)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                      UnaryHistory endpointRead ∧ UnaryHistory closedNormalRead ∧
                        UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateRoute finishedRoute endpointRoute closedNormalRoute structuralRoute
    structuralPkg
  have carrierPacket :
      MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg :=
    carrier
  rcases carrier with
    ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
      _obstructionUnary, _transportUnary, replayUnary, provenanceUnary, localRowUnary,
      _carrierCandidateRoute, _carrierFinishedRoute, _carrierEndpointRoute,
      _transportSame, provenancePkg⟩
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateRoute
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointRoute
  have closedNormalReadUnary : UnaryHistory closedNormalRead :=
    unary_cont_closed endpointReadUnary provenanceUnary closedNormalRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed localRowUnary closedNormalReadUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
              obstruction transport replay provenance localRow bundle pkg ∧ hsame row localRow)
          (fun row : BHist =>
            hsame row localRow ∧ UnaryHistory row ∧
              Cont candidate closedCandidate candidateRead ∧ Cont finished endpoint finishedRead ∧
                Cont endpoint replay endpointRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle structuralRead pkg ∧
              hsame row localRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro localRow ⟨carrierPacket, hsame_refl localRow⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport localRowUnary (hsame_symm source.right),
            candidateRoute, finishedRoute, endpointRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, structuralPkg, source.right⟩
    }
  exact
    ⟨cert, candidateReadUnary, finishedReadUnary, endpointReadUnary, closedNormalReadUnary,
      structuralReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
