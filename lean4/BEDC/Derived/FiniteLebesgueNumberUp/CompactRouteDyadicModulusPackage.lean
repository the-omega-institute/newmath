import BEDC.Derived.FiniteLebesgueNumberUp.UniformModulusConsumerExactness

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactRouteDyadicModulusPackage_certificate [AskSetup]
    [PackageSetup]
    {cover radius mesh stream regular real selector transport replay provenance nameRow folded
      compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRadiusLowerBoundFold cover radius mesh stream regular real selector
        transport replay provenance nameRow folded bundle pkg ->
      Cont folded selector compactRead ->
        PkgSig bundle compactRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row folded ∨ hsame row compactRead)
              (fun row : BHist =>
                hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨
                  hsame row folded ∨ Cont folded selector compactRead)
              (fun row : BHist =>
                PkgSig bundle compactRead pkg ∧
                  (hsame row folded ∨ hsame row compactRead))
              hsame ∧
            UnaryHistory folded ∧ UnaryHistory compactRead ∧
              Cont folded selector compactRead ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fold foldedSelectorCompact compactPkg
  obtain ⟨carrier, coverRadiusFolded, _foldedMeshStream, _streamRegularReal,
    realSelectorFolded, _foldedPkg⟩ := fold
  obtain ⟨coverUnary, _streamUnary, radiusUnary, _meshUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameRowUnary, _coverStreamRadius,
    _radiusMeshReplay, _replayNameProvenance, _provenancePkg⟩ := carrier
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed coverUnary radiusUnary coverRadiusFolded
  have selectorUnary : UnaryHistory selector :=
    unary_cont_right_factor realSelectorFolded foldedUnary
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed foldedUnary selectorUnary foldedSelectorCompact
  have sourceAtCompact :
      (fun row : BHist => hsame row folded ∨ hsame row compactRead) compactRead := by
    exact Or.inr (hsame_refl compactRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row folded ∨ hsame row compactRead)
          (fun row : BHist =>
            hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row folded ∨ Cont folded selector compactRead)
          (fun row : BHist =>
            PkgSig bundle compactRead pkg ∧
              (hsame row folded ∨ hsame row compactRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead sourceAtCompact
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
        cases source with
        | inl rowFolded =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowFolded)
        | inr rowCompact =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) rowCompact)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowFolded =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rowFolded)))
      | inr _rowCompact =>
          exact Or.inr (Or.inr (Or.inr (Or.inr foldedSelectorCompact)))
    ledger_sound := by
      intro _row source
      exact ⟨compactPkg, source⟩
  }
  exact ⟨cert, foldedUnary, compactUnary, foldedSelectorCompact, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
