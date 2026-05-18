import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obstruction_scope_stability
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow obstructionRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont obstruction transport obstructionRead ->
        Cont obstructionRead localRow scopedRead ->
          PkgSig bundle scopedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row obstruction ∧ Cont obstruction transport obstructionRead ∧
                    Cont obstructionRead localRow scopedRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle scopedRead pkg ∧
                    hsame row obstruction)
                hsame ∧
              UnaryHistory obstructionRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier obstructionTransportRead obstructionLocalScoped scopedPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, transportUnary, _replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed obstructionReadUnary localRowUnary obstructionLocalScoped
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∧ Cont obstruction transport obstructionRead ∧
              Cont obstructionRead localRow scopedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle scopedRead pkg ∧
              hsame row obstruction)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstruction
        ⟨hsame_refl obstruction, obstructionUnary⟩
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
      exact ⟨source.left, obstructionTransportRead, obstructionLocalScoped⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, scopedPkg, source.left⟩
  }
  exact ⟨cert, obstructionReadUnary, scopedReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
