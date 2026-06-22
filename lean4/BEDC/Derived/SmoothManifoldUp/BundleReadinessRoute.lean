import BEDC.Derived.SmoothManifoldUp.TasteGate

namespace BEDC.Derived.SmoothManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SmoothManifoldBundleReadinessRoute [AskSetup] [PackageSetup]
    {base topology model atlas overlap transition readiness transport replay provenance
      localName atlasRead bundleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SmoothManifoldCarrier base topology model atlas overlap transition readiness transport replay
        provenance localName bundle pkg →
      Cont atlas transition atlasRead →
        Cont atlasRead readiness bundleRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle bundleRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row atlas ∨ hsame row transition ∨ hsame row atlasRead ∨
                        hsame row bundleRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row base ∨ hsame row topology ∨ hsame row model ∨
                      hsame row atlas ∨ hsame row overlap ∨ hsame row transition ∨
                        hsame row readiness ∨ hsame row atlasRead ∨ hsame row bundleRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont atlas transition atlasRead ∧
                      Cont atlasRead readiness bundleRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle bundleRead pkg)
                  hsame ∧
                UnaryHistory atlasRead ∧ UnaryHistory bundleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier atlasTransitionRead atlasReadinessBundle _provenancePkg bundlePkg
  obtain ⟨_baseUnary, _topologyUnary, _modelUnary, atlasUnary, _overlapUnary,
    transitionUnary, readinessUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, carrierProvenancePkg⟩ := carrier
  have atlasReadUnary : UnaryHistory atlasRead :=
    unary_cont_closed atlasUnary transitionUnary atlasTransitionRead
  have bundleReadUnary : UnaryHistory bundleRead :=
    unary_cont_closed atlasReadUnary readinessUnary atlasReadinessBundle
  have sourceAtBundleRead :
      (fun row : BHist =>
        (hsame row atlas ∨ hsame row transition ∨ hsame row atlasRead ∨
            hsame row bundleRead) ∧
          UnaryHistory row) bundleRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (hsame_refl bundleRead))), bundleReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row atlas ∨ hsame row transition ∨ hsame row atlasRead ∨
                hsame row bundleRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row base ∨ hsame row topology ∨ hsame row model ∨ hsame row atlas ∨
              hsame row overlap ∨ hsame row transition ∨ hsame row readiness ∨
                hsame row atlasRead ∨ hsame row bundleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont atlas transition atlasRead ∧
              Cont atlasRead readiness bundleRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle bundleRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro bundleRead sourceAtBundleRead
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl rowAtlas =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowAtlas)
          | inr sourceTail =>
              cases sourceTail with
              | inl rowTransition =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowTransition))
              | inr sourceTail =>
                  cases sourceTail with
                  | inl rowAtlasRead =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) rowAtlasRead)))
                  | inr rowBundleRead =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) rowBundleRead)))
        · exact unary_transport source.right sameRows
    · intro _row source
      cases source.left with
      | inl rowAtlas =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rowAtlas)))
      | inr sourceTail =>
          cases sourceTail with
          | inl rowTransition =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowTransition)))))
          | inr sourceTail =>
              cases sourceTail with
              | inl rowAtlasRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr (Or.inl rowAtlasRead)))))))
              | inr rowBundleRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr rowBundleRead)))))))
    · intro _row source
      exact
        ⟨source.right, atlasTransitionRead, atlasReadinessBundle, carrierProvenancePkg,
          bundlePkg⟩
  exact ⟨cert, atlasReadUnary, bundleReadUnary⟩

end BEDC.Derived.SmoothManifoldUp
