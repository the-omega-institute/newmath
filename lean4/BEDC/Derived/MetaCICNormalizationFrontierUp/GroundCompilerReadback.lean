import BEDC.Derived.MetaCICNormalizationFrontierUp.GroundCompilerRoute

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierGroundCompilerReadback [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      Cont normalRead provenance auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory auditRead ∧
            SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
                  hsame row auditRead)
              (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro target normalProvenance auditPkg
  have targetPacket :
      MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg :=
    target
  obtain ⟨carrier, _candidateClosedRead, _finishedEndpointRead, _finishedReplayEndpoint,
    _endpointLocalNormal, _endpointReplayEndpoint, _endpointLocalSubstitution, _normalPkg,
    _substitutionPkg⟩ := target
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, _replayUnary, provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkgFromCarrier⟩ := carrier
  have targetScope :=
    MetaCICNormalizationFrontierGroundCompilerTargetScope
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (endpointRead := endpointRead) (normalRead := normalRead)
      (substitutionRead := substitutionRead) (bundle := bundle) (pkg := pkg)
      targetPacket
  obtain ⟨_normalCert, _candidateReadUnary, _finishedReadUnary, _endpointReadUnary,
    normalReadUnary, _substitutionReadUnary, _transportSameCandidateFinished,
    provenancePkg⟩ := targetScope
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed normalReadUnary provenanceUnary normalProvenance
  have auditSource :
      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row) auditRead := by
    exact ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
              hsame row auditRead)
          (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead auditSource
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨auditPkg, source.left⟩
  }
  exact ⟨auditUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
