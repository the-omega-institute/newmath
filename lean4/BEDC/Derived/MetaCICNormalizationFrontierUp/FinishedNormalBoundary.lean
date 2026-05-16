import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_finished_normal_boundary [AskSetup]
    [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow endpointRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont finished endpoint endpointRead ->
        Cont obstruction transport obstructionRead ->
          Cont endpointRead replay publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory endpointRead ∧ UnaryHistory obstructionRead ∧
                UnaryHistory publicRead ∧ Cont finished endpoint endpointRead ∧
                  Cont obstruction transport obstructionRead ∧
                    Cont endpointRead replay publicRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row endpointRead ∨ hsame row obstructionRead ∨
                            hsame row publicRead)
                        (fun row : BHist => PkgSig bundle publicRead pkg ∧
                          hsame row publicRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier finishedEndpointRead obstructionTransportRead endpointReplayPublic publicPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary replayUnary endpointReplayPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row endpointRead ∨ hsame row obstructionRead ∨ hsame row publicRead)
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
  exact
    ⟨endpointReadUnary, obstructionReadUnary, publicReadUnary, finishedEndpointRead,
      obstructionTransportRead, endpointReplayPublic, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
