import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCarrier_definition_surface [AskSetup] [PackageSetup]
    {U F E R W D S H C P N definitionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U N definitionRead ->
        PkgSig bundle definitionRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row definitionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                  hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row definitionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont U F E ∧ Cont E R W ∧ Cont W D S ∧
                  Cont U N definitionRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle definitionRead pkg)
              hsame ∧ UnaryHistory definitionRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier definitionRoute definitionPkg
  obtain ⟨unaryU, _unaryF, _unaryE, _unaryR, _unaryW, _unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, routeE, routeW, routeS, provenancePkg, localNamePkg⟩ :=
    carrier
  have definitionUnary : UnaryHistory definitionRead :=
    unary_cont_closed unaryU unaryN definitionRoute
  have sourceAtDefinition :
      (fun row : BHist => hsame row definitionRead ∧ UnaryHistory row)
        definitionRead := by
    exact ⟨hsame_refl definitionRead, definitionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row definitionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row definitionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F E ∧ Cont E R W ∧ Cont W D S ∧
              Cont U N definitionRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle definitionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro definitionRead sourceAtDefinition
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
      repeat right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeE, routeW, routeS, definitionRoute, provenancePkg,
          localNamePkg, definitionPkg⟩
  }
  exact ⟨cert, definitionUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
