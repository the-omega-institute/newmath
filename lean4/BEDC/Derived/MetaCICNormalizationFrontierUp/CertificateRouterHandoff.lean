import BEDC.Derived.MetaCICNormalizationFrontierUp.GroundCompilerReadback

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCertificateRouterHandoff [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead normalRead substitutionRead auditRead routerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      Cont normalRead provenance auditRead →
        Cont auditRead localRow routerRead →
          PkgSig bundle auditRead pkg →
            PkgSig bundle routerRead pkg →
              UnaryHistory routerRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row routerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
                      hsame row auditRead ∨ hsame row routerRead)
                  (fun row : BHist => PkgSig bundle routerRead pkg ∧ hsame row routerRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro target normalProvenance auditLocal auditPkg routerPkg
  have targetPacket :
      MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg :=
    target
  have readback :=
    MetaCICNormalizationFrontierGroundCompilerReadback
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (endpointRead := endpointRead) (normalRead := normalRead)
      (substitutionRead := substitutionRead) (auditRead := auditRead) (bundle := bundle)
      (pkg := pkg) targetPacket normalProvenance auditPkg
  obtain ⟨carrier, _candidateClosedRead, _finishedEndpointRead, _finishedReplayEndpoint,
    _endpointLocalNormal, _endpointReplayEndpoint, _endpointLocalSubstitution, _normalPkg,
    _substitutionPkg⟩ := targetPacket
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkgFromCarrier⟩ := carrier
  obtain ⟨auditUnary, _auditCert⟩ := readback
  have routerUnary : UnaryHistory routerRead :=
    unary_cont_closed auditUnary localRowUnary auditLocal
  have routerSource :
      (fun row : BHist => hsame row routerRead ∧ UnaryHistory row) routerRead := by
    exact ⟨hsame_refl routerRead, routerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
              hsame row auditRead ∨ hsame row routerRead)
          (fun row : BHist => PkgSig bundle routerRead pkg ∧ hsame row routerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routerRead routerSource
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
      exact ⟨routerPkg, source.left⟩
  }
  exact ⟨routerUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
