import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obstruction_visible_transport
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead obstructionRead visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont obstructionRead replay visibleRead ->
              PkgSig bundle visibleRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory visibleRead ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row visibleRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row endpointRead ∨
                          hsame row obstructionRead ∨ hsame row visibleRead)
                      (fun row : BHist =>
                        PkgSig bundle visibleRead pkg ∧ hsame row visibleRead)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    obstructionReplayVisible visiblePkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayVisible
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row visibleRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row obstructionRead ∨
            hsame row visibleRead)
        (fun row : BHist => PkgSig bundle visibleRead pkg ∧ hsame row visibleRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro visibleRead ⟨hsame_refl visibleRead, visibleReadUnary⟩
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
        exact ⟨visiblePkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionReadUnary, visibleReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
