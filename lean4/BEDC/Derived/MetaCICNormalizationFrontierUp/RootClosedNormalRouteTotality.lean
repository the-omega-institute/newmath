import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_closed_normal_route_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead closedNormalRead obstructionRoute publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead finishedRead closedNormalRead ->
            Cont obstruction replay obstructionRoute ->
              Cont closedNormalRead obstructionRoute publicRead ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row finishedRead ∨
                          hsame row obstructionRoute ∨ hsame row publicRead)
                      (fun row : BHist =>
                        PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                      UnaryHistory closedNormalRead ∧ UnaryHistory obstructionRoute ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidateFinishedClosed
    obstructionReplayRoute closedObstructionPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have closedNormalReadUnary : UnaryHistory closedNormalRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedClosed
  have obstructionRouteUnary : UnaryHistory obstructionRoute :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed closedNormalReadUnary obstructionRouteUnary closedObstructionPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row finishedRead ∨
            hsame row obstructionRoute ∨ hsame row publicRead)
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.left⟩
    }
  exact
    ⟨cert, candidateReadUnary, finishedReadUnary, closedNormalReadUnary,
      obstructionRouteUnary, publicReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
