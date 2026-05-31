import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberRadiusLowerBoundFold [AskSetup] [PackageSetup]
    (cover radius mesh stream regular real selector transport replay provenance
      nameRow folded : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance nameRow
      bundle pkg ∧
    Cont cover radius folded ∧ Cont folded mesh stream ∧ Cont stream regular real ∧
      Cont real selector folded ∧ PkgSig bundle folded pkg

theorem FiniteLebesgueNumberUniformModulusConsumerExactness [AskSetup] [PackageSetup]
    {cover radius mesh stream regular real selector transport replay provenance nameRow folded
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRadiusLowerBoundFold cover radius mesh stream regular real selector
        transport replay provenance nameRow folded bundle pkg ->
      Cont folded selector uniformRead ->
        PkgSig bundle uniformRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row folded ∨ hsame row uniformRead)
              (fun row : BHist =>
                hsame row radius ∨ hsame row folded ∨ Cont folded selector uniformRead)
              (fun row : BHist =>
                PkgSig bundle uniformRead pkg ∧
                  (hsame row folded ∨ hsame row uniformRead))
              hsame ∧
            UnaryHistory folded ∧ UnaryHistory uniformRead ∧
              Cont folded selector uniformRead ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fold foldedSelectorUniform uniformPkg
  obtain ⟨carrier, coverRadiusFolded, foldedMeshStream, streamRegularReal,
    realSelectorFolded, _foldedPkg⟩ := fold
  obtain ⟨coverUnary, _streamUnary, radiusUnary, _meshUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameRowUnary, _coverStreamRadius,
    _radiusMeshReplay, _replayNameProvenance, _provenancePkg⟩ := carrier
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed coverUnary radiusUnary coverRadiusFolded
  have selectorUnary : UnaryHistory selector :=
    unary_cont_right_factor realSelectorFolded foldedUnary
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed foldedUnary selectorUnary foldedSelectorUniform
  have sourceAtUniform :
      (fun row : BHist => hsame row folded ∨ hsame row uniformRead) uniformRead := by
    exact Or.inr (hsame_refl uniformRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row folded ∨ hsame row uniformRead)
          (fun row : BHist =>
            hsame row radius ∨ hsame row folded ∨ Cont folded selector uniformRead)
          (fun row : BHist =>
            PkgSig bundle uniformRead pkg ∧
              (hsame row folded ∨ hsame row uniformRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceAtUniform
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
        | inr rowUniform =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) rowUniform)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowFolded =>
          exact Or.inr (Or.inl rowFolded)
      | inr _rowUniform =>
          exact Or.inr (Or.inr foldedSelectorUniform)
    ledger_sound := by
      intro _row source
      exact ⟨uniformPkg, source⟩
  }
  exact ⟨cert, foldedUnary, uniformUnary, foldedSelectorUniform, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
