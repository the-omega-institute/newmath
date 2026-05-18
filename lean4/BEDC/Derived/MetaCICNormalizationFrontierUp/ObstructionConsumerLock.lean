import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obstruction_consumer_lock
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRead candidateLocked endpointLocked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont candidateRead obstructionRead candidateLocked ->
              Cont endpointRead obstructionRead endpointLocked ->
                PkgSig bundle candidateLocked pkg ->
                  PkgSig bundle endpointLocked pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateRead ∨ hsame row endpointRead ∨
                            hsame row obstructionRead ∨ hsame row candidateLocked ∨
                              hsame row endpointLocked)
                        (fun row : BHist =>
                          PkgSig bundle candidateLocked pkg ∧
                            PkgSig bundle endpointLocked pkg ∧ hsame row obstructionRead)
                        hsame ∧
                      UnaryHistory obstructionRead ∧ UnaryHistory candidateLocked ∧
                        UnaryHistory endpointLocked := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    candidateObstructionLocked endpointObstructionLocked candidateLockedPkg endpointLockedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have candidateLockedUnary : UnaryHistory candidateLocked :=
    unary_cont_closed candidateReadUnary obstructionReadUnary candidateObstructionLocked
  have endpointLockedUnary : UnaryHistory endpointLocked :=
    unary_cont_closed endpointReadUnary obstructionReadUnary endpointObstructionLocked
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row obstructionRead ∨
              hsame row candidateLocked ∨ hsame row endpointLocked)
          (fun row : BHist =>
            PkgSig bundle candidateLocked pkg ∧ PkgSig bundle endpointLocked pkg ∧
              hsame row obstructionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro obstructionRead ⟨hsame_refl obstructionRead, obstructionReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inl source.left))
      ledger_sound := by
        intro _row source
        exact ⟨candidateLockedPkg, endpointLockedPkg, source.left⟩
    }
  exact ⟨cert, obstructionReadUnary, candidateLockedUnary, endpointLockedUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
