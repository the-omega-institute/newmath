import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCandidateEndpointPremiseRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead premiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont endpoint replay endpointRead →
          Cont candidateRead endpointRead premiseRead →
            PkgSig bundle premiseRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row premiseRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidate ∨ hsame row closedCandidate ∨
                      hsame row endpoint ∨ hsame row obstruction ∨
                        hsame row premiseRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle premiseRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory premiseRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier candidateClosedRead endpointReplayRead candidateEndpointPremise premisePkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have premiseReadUnary : UnaryHistory premiseRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointPremise
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row premiseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row closedCandidate ∨ hsame row endpoint ∨
              hsame row obstruction ∨ hsame row premiseRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle premiseRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro premiseRead ⟨hsame_refl premiseRead, premiseReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, premisePkg⟩
  }
  exact ⟨cert, candidateReadUnary, endpointReadUnary, premiseReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
