import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_finished_route_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow finishedRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory publicRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row finishedRead ∨ hsame row endpointRead ∨
                        hsame row publicRead)
                    (fun row : BHist =>
                      PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier finishedEndpointRead finishedReplayEndpoint endpointLocalPublic publicPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row finishedRead ∨ hsame row endpointRead ∨ hsame row publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.left⟩
    }
  exact ⟨finishedReadUnary, endpointReadUnary, publicReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
