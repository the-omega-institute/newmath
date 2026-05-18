import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_root_normal_endpoint_route_exhaustion
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow finishedRead endpointRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont finished endpoint finishedRead ->
        Cont finishedRead replay endpointRead ->
          Cont endpointRead localRow rootRead ->
            PkgSig bundle rootRead pkg ->
              UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory rootRead ∧ hsame transport (append candidate finished) ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row finishedRead ∨ hsame row endpointRead ∨
                        hsame row obstruction ∨ hsame row rootRead)
                    (fun row : BHist =>
                      PkgSig bundle rootRead pkg ∧ hsame row rootRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier finishedEndpointRead finishedReplayEndpoint endpointLocalRoot rootPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalRoot
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row finishedRead ∨ hsame row endpointRead ∨ hsame row obstruction ∨
            hsame row rootRead)
        (fun row : BHist => PkgSig bundle rootRead pkg ∧ hsame row rootRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro rootRead ⟨hsame_refl rootRead, rootReadUnary⟩
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
        exact ⟨rootPkg, source.left⟩
    }
  exact
    ⟨finishedReadUnary, endpointReadUnary, rootReadUnary,
      transportSameCandidateFinished, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
