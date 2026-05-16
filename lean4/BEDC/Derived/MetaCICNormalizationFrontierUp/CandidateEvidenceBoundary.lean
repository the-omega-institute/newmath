import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_candidate_evidence_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead sealedRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont candidateRead obstruction sealedRead ->
          Cont sealedRead replay routeRead ->
            PkgSig bundle routeRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory sealedRead ∧
                UnaryHistory routeRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row sealedRead ∨
                        hsame row routeRead)
                    (fun row : BHist =>
                      PkgSig bundle routeRead pkg ∧ hsame row routeRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead candidateObstructionSeal sealedReplayRoute routePkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed candidateReadUnary obstructionUnary candidateObstructionSeal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sealedReadUnary replayUnary sealedReplayRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row sealedRead ∨ hsame row routeRead)
        (fun row : BHist => PkgSig bundle routeRead pkg ∧ hsame row routeRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
        exact ⟨routePkg, source.left⟩
    }
  exact ⟨candidateReadUnary, sealedReadUnary, routeReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
