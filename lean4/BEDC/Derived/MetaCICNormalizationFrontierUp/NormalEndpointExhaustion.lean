import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierNormalEndpointExhaustion [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      finishedRead endpointRead supportRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow supportRead ->
            Cont supportRead obstruction finalRead ->
              PkgSig bundle finalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row finishedRead ∨ hsame row endpointRead ∨
                        hsame row supportRead ∨ hsame row finalRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg ∧
                        hsame row endpointRead)
                    hsame ∧
                  UnaryHistory supportRead ∧ UnaryHistory finalRead ∧
                    Cont finished endpoint finishedRead ∧
                      Cont finishedRead replay endpointRead ∧
                        Cont endpointRead localRow supportRead ∧
                          Cont supportRead obstruction finalRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier finishedEndpointRead finishedReplayEndpoint endpointLocalSupport
    supportObstructionFinal finalReadPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalSupport
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed supportReadUnary obstructionUnary supportObstructionFinal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row finishedRead ∨ hsame row endpointRead ∨
              hsame row supportRead ∨ hsame row finalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg ∧
              hsame row endpointRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, finalReadPkg, source.left⟩
  }
  exact
    ⟨cert, supportReadUnary, finalReadUnary, finishedEndpointRead, finishedReplayEndpoint,
      endpointLocalSupport, supportObstructionFinal⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
