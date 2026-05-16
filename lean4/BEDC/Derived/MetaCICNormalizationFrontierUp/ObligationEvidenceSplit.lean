import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obligation_evidence_split [AskSetup]
    [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          PkgSig bundle candidateRead pkg ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateRead ∨ hsame row endpointRead) ∧ UnaryHistory row)
                  (fun row : BHist => hsame row candidateRead ∨ hsame row endpointRead)
                  (fun row : BHist =>
                    (PkgSig bundle candidateRead pkg ∧ hsame row candidateRead) ∨
                      (PkgSig bundle endpointRead pkg ∧ hsame row endpointRead))
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidatePkg endpointPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          (hsame row candidateRead ∨ hsame row endpointRead) ∧ UnaryHistory row)
        (fun row : BHist => hsame row candidateRead ∨ hsame row endpointRead)
        (fun row : BHist =>
          (PkgSig bundle candidateRead pkg ∧ hsame row candidateRead) ∨
            (PkgSig bundle endpointRead pkg ∧ hsame row endpointRead))
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro candidateRead ⟨Or.inl (hsame_refl candidateRead), candidateReadUnary⟩
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
          constructor
          · cases source.left with
            | inl candidateSame =>
                exact Or.inl (hsame_trans (hsame_symm same) candidateSame)
            | inr endpointSame =>
                exact Or.inr (hsame_trans (hsame_symm same) endpointSame)
          · exact unary_transport source.right same
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        cases source.left with
        | inl candidateSame =>
            exact Or.inl ⟨candidatePkg, candidateSame⟩
        | inr endpointSame =>
            exact Or.inr ⟨endpointPkg, endpointSame⟩
    }
  exact ⟨candidateReadUnary, endpointReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
