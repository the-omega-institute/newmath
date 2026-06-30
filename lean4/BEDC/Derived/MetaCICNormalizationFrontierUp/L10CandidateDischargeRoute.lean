import BEDC.Derived.MetaCICNormalizationFrontierUp.DischargeRoute

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierL10CandidateDischargeRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead endpointRead normalRead substitutionRead dischargeRead l10Source
      auditRead sealedRead closedNormalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg ->
      Cont normalRead substitutionRead dischargeRead ->
        Cont candidateRead endpointRead l10Source ->
          Cont dischargeRead l10Source auditRead ->
            Cont auditRead replay sealedRead ->
              Cont sealedRead localRow closedNormalRead ->
                PkgSig bundle closedNormalRead pkg ->
                  SemanticNameCert
                        (fun row : BHist => hsame row closedNormalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row normalRead ∨ hsame row substitutionRead ∨
                            hsame row dischargeRead ∨ hsame row l10Source ∨
                              hsame row auditRead ∨ hsame row sealedRead ∨
                                hsame row closedNormalRead)
                        (fun row : BHist =>
                          PkgSig bundle closedNormalRead pkg ∧
                            hsame row closedNormalRead)
                        hsame ∧
                    UnaryHistory dischargeRead ∧ UnaryHistory l10Source ∧
                      UnaryHistory auditRead ∧ UnaryHistory sealedRead ∧
                        UnaryHistory closedNormalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro target normalSubstitutionDischarge candidateEndpointL10 dischargeL10Audit
    auditReplaySeal sealedLocalClosedNormal closedNormalPkg
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
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  obtain ⟨_scopeCert, candidateReadUnary, _finishedReadUnary, endpointReadUnary,
    normalReadUnary, substitutionReadUnary, _transportSameCandidateFinished,
    _provenancePkg⟩ := scope
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed normalReadUnary substitutionReadUnary normalSubstitutionDischarge
  have l10Unary : UnaryHistory l10Source :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointL10
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed dischargeUnary l10Unary dischargeL10Audit
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed auditUnary replayUnary auditReplaySeal
  have closedNormalUnary : UnaryHistory closedNormalRead :=
    unary_cont_closed sealedUnary localRowUnary sealedLocalClosedNormal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closedNormalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normalRead ∨ hsame row substitutionRead ∨
              hsame row dischargeRead ∨ hsame row l10Source ∨ hsame row auditRead ∨
                hsame row sealedRead ∨ hsame row closedNormalRead)
          (fun row : BHist =>
            PkgSig bundle closedNormalRead pkg ∧ hsame row closedNormalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro closedNormalRead
            ⟨hsame_refl closedNormalRead, closedNormalUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨closedNormalPkg, source.left⟩
    }
  exact ⟨cert, dischargeUnary, l10Unary, auditUnary, sealedUnary, closedNormalUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
