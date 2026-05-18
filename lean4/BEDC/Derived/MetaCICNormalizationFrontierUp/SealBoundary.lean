import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_seal_boundary [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead normalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint normalRead ->
          Cont candidateRead obstruction sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory normalRead ∧ UnaryHistory sealRead ∧
                hsame transport (append candidate finished) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row normalRead ∨ hsame row sealRead)
                      (fun row : BHist => PkgSig bundle sealRead pkg ∧ hsame row sealRead)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidateObstructionSeal sealPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed candidateReadUnary obstructionUnary candidateObstructionSeal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row normalRead ∨ hsame row sealRead)
        (fun row : BHist => PkgSig bundle sealRead pkg ∧ hsame row sealRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        exact ⟨sealPkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary, normalReadUnary, sealReadUnary, transportSameCandidateFinished,
      provenancePkg, sealPkg, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
