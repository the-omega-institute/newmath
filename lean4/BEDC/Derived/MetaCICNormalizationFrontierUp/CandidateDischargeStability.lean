import BEDC.Derived.MetaCICNormalizationFrontierUp.GroundCompilerRoute

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCandidateDischargeStability [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead candidateRead'
      finishedRead' endpointRead' normalRead' substitutionRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      hsame candidateRead candidateRead' →
        hsame finishedRead finishedRead' →
          hsame endpointRead endpointRead' →
            hsame normalRead normalRead' →
              hsame substitutionRead substitutionRead' →
                UnaryHistory candidateRead' ∧ UnaryHistory finishedRead' ∧
                  UnaryHistory endpointRead' ∧ UnaryHistory normalRead' ∧
                    UnaryHistory substitutionRead' ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row normalRead' ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateRead' ∨ hsame row finishedRead' ∨
                            hsame row endpointRead' ∨ hsame row normalRead' ∨
                              hsame row substitutionRead')
                        (fun row : BHist =>
                          PkgSig bundle normalRead pkg ∧
                            PkgSig bundle substitutionRead pkg ∧ hsame row normalRead')
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro target candidateSame finishedSame endpointSame normalSame substitutionSame
  have scope :=
    MetaCICNormalizationFrontierGroundCompilerTargetScope
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (endpointRead := endpointRead) (normalRead := normalRead)
      (substitutionRead := substitutionRead) (bundle := bundle) (pkg := pkg) target
  obtain ⟨_scopeCert, candidateReadUnary, finishedReadUnary, endpointReadUnary,
    normalReadUnary, substitutionReadUnary, _transportSameCandidateFinished,
    _provenancePkg⟩ := scope
  obtain ⟨_carrier, _candidateClosedRead, _finishedEndpointRead, _finishedReplayEndpoint,
    _endpointLocalNormal, _endpointReplayEndpoint, _endpointLocalSubstitution, normalPkg,
    substitutionPkg⟩ := target
  have candidateReadUnary' : UnaryHistory candidateRead' :=
    unary_transport candidateReadUnary candidateSame
  have finishedReadUnary' : UnaryHistory finishedRead' :=
    unary_transport finishedReadUnary finishedSame
  have endpointReadUnary' : UnaryHistory endpointRead' :=
    unary_transport endpointReadUnary endpointSame
  have normalReadUnary' : UnaryHistory normalRead' :=
    unary_transport normalReadUnary normalSame
  have substitutionReadUnary' : UnaryHistory substitutionRead' :=
    unary_transport substitutionReadUnary substitutionSame
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row normalRead' ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead' ∨ hsame row finishedRead' ∨
            hsame row endpointRead' ∨ hsame row normalRead' ∨ hsame row substitutionRead')
        (fun row : BHist =>
          PkgSig bundle normalRead pkg ∧ PkgSig bundle substitutionRead pkg ∧
            hsame row normalRead')
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro normalRead' ⟨hsame_refl normalRead', normalReadUnary'⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨normalPkg, substitutionPkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary', finishedReadUnary', endpointReadUnary', normalReadUnary',
      substitutionReadUnary', cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
