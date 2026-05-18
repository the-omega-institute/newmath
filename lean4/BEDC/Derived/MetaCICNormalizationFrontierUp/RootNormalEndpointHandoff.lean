import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierRootNormalEndpointHandoff [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow finishedRead endpointRead supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow supportRead ->
            PkgSig bundle supportRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row finishedRead ∨ hsame row endpointRead ∨
                      hsame row supportRead)
                  (fun row : BHist =>
                    PkgSig bundle supportRead pkg ∧ hsame row supportRead)
                  hsame ∧
                UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory supportRead ∧ Cont finished endpoint finishedRead ∧
                    Cont finishedRead replay endpointRead ∧
                      Cont endpointRead localRow supportRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier finishedEndpointRead finishedReplayEndpoint endpointLocalSupport supportPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalSupport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row finishedRead ∨ hsame row endpointRead ∨ hsame row supportRead)
          (fun row : BHist => PkgSig bundle supportRead pkg ∧ hsame row supportRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro supportRead ⟨hsame_refl supportRead, supportReadUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨supportPkg, source.left⟩
  }
  exact
    ⟨cert, finishedReadUnary, endpointReadUnary, supportReadUnary, finishedEndpointRead,
      finishedReplayEndpoint, endpointLocalSupport, provenancePkg, supportPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
