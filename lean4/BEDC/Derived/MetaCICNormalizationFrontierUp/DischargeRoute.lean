import BEDC.Derived.MetaCICNormalizationFrontierUp.GroundCompilerRoute

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierDischargeRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead dischargeRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      Cont normalRead substitutionRead dischargeRead →
        PkgSig bundle dischargeRead pkg →
          UnaryHistory dischargeRead ∧
            SemanticNameCert
              (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
                  hsame row normalRead ∨ hsame row substitutionRead ∨ hsame row dischargeRead)
              (fun row : BHist => PkgSig bundle dischargeRead pkg ∧ hsame row dischargeRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro target normalSubstitutionDischarge dischargePkg
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
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed normalReadUnary substitutionReadUnary normalSubstitutionDischarge
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
            hsame row normalRead ∨ hsame row substitutionRead ∨ hsame row dischargeRead)
        (fun row : BHist => PkgSig bundle dischargeRead pkg ∧ hsame row dischargeRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro dischargeRead ⟨hsame_refl dischargeRead, dischargeUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨dischargePkg, source.left⟩
    }
  exact ⟨dischargeUnary, cert⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
