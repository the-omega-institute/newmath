import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_candidate_obstruction_separation
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont obstruction transport obstructionRead →
          Cont candidateRead replay publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory candidateRead ∧ UnaryHistory obstructionRead ∧
                UnaryHistory publicRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row obstructionRead ∨
                        hsame row publicRead)
                    (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead obstructionTransportRead candidateReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayPublic
  have cert :
      SemanticNameCert (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row obstructionRead ∨ hsame row publicRead)
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
  exact ⟨candidateReadUnary, obstructionReadUnary, publicReadUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
