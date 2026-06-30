import BEDC.Derived.MetaCICNormalizationFrontierUp.GroundCompilerRoute

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierFormalTargetContract [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead residualRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      Cont normalRead obstruction residualRead →
        Cont normalRead provenance auditRead →
          PkgSig bundle residualRead pkg →
            PkgSig bundle auditRead pkg →
              UnaryHistory residualRead ∧ UnaryHistory auditRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
                      hsame row residualRead ∨ hsame row auditRead)
                  (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro target normalObstructionResidual normalProvenanceAudit _residualPkg auditPkg
  have scope :=
    MetaCICNormalizationFrontierGroundCompilerTargetScope
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (endpointRead := endpointRead) (normalRead := normalRead)
      (substitutionRead := substitutionRead) (bundle := bundle) (pkg := pkg) target
  obtain ⟨carrier, _candidateClosedRead, _finishedEndpointRead, _finishedReplayEndpoint,
    _endpointLocalNormal, _endpointReplayEndpoint, _endpointLocalSubstitution, _normalPkg,
    _substitutionPkg⟩ := target
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, _transportUnary, _replayUnary, provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  obtain ⟨_scopeCert, _candidateReadUnary, _finishedReadUnary, _endpointReadUnary,
    normalReadUnary, _substitutionReadUnary, _transportSameCandidateFinished,
    _provenancePkg⟩ := scope
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed normalReadUnary obstructionUnary normalObstructionResidual
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed normalReadUnary provenanceUnary normalProvenanceAudit
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row normalRead ∨
            hsame row residualRead ∨ hsame row auditRead)
        (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨auditPkg, source.left⟩
    }
  exact ⟨residualUnary, auditUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
