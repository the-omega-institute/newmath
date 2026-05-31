import BEDC.Derived.FiniteLebesgueNumberUp.UniformModulusConsumerExactness

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberScopedClosurePackage [AskSetup] [PackageSetup]
    {cover radius mesh stream regular real selector transport replay provenance nameRow
      folded compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRadiusLowerBoundFold cover radius mesh stream regular real selector
        transport replay provenance nameRow folded bundle pkg ->
      Cont folded selector compactRead ->
        Cont compactRead mesh uniformRead ->
          PkgSig bundle uniformRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row folded ∨ hsame row compactRead ∨ hsame row uniformRead ∨
                    Cont folded selector compactRead ∨ Cont compactRead mesh uniformRead)
                (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                hsame ∧
              UnaryHistory folded ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                Cont folded selector compactRead ∧ Cont compactRead mesh uniformRead ∧
                  PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fold foldedSelectorCompact compactMeshUniform uniformPkg
  obtain ⟨carrier, coverRadiusFolded, _foldedMeshStream, _streamRegularReal,
    realSelectorFolded, _foldedPkg⟩ := fold
  obtain ⟨coverUnary, _streamUnary, radiusUnary, meshUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameRowUnary, _coverStreamRadius,
    _radiusMeshReplay, _replayNameProvenance, _provenancePkg⟩ := carrier
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed coverUnary radiusUnary coverRadiusFolded
  have selectorUnary : UnaryHistory selector :=
    unary_cont_right_factor realSelectorFolded foldedUnary
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed foldedUnary selectorUnary foldedSelectorCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary meshUnary compactMeshUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row folded ∨ hsame row compactRead ∨ hsame row uniformRead ∨
              Cont folded selector compactRead ∨ Cont compactRead mesh uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact
    ⟨cert, foldedUnary, compactUnary, uniformUnary, foldedSelectorCompact,
      compactMeshUniform, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
