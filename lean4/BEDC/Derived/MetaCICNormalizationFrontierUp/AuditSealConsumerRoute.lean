import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierAuditSealConsumerRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction replay obstructionRead ->
            Cont candidateRead finishedRead auditRead ->
              PkgSig bundle auditRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      MetaCICNormalizationFrontierCarrier candidate closedCandidate finished
                        endpoint obstruction transport replay provenance localRow bundle pkg ∧
                        hsame row auditRead)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row finishedRead ∨
                        hsame row obstructionRead ∨ hsame row auditRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                        hsame row auditRead)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory obstructionRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier candidateClosedRead finishedEndpointRead obstructionReplayRead
    candidateFinishedAudit auditPkg
  have carrierPacket :
      MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg :=
    carrier
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary replayUnary obstructionReplayRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
              obstruction transport replay provenance localRow bundle pkg ∧
              hsame row auditRead)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row finishedRead ∨
              hsame row obstructionRead ∨ hsame row auditRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              hsame row auditRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro auditRead ⟨carrierPacket, hsame_refl auditRead⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.right))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditPkg, source.right⟩
    }
  exact ⟨cert, candidateReadUnary, finishedReadUnary, obstructionReadUnary, auditReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
