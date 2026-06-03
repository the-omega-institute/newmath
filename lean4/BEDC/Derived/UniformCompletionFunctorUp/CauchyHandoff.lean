import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCarrier_cauchy_handoff [AskSetup] [PackageSetup]
    {U F E R W D S H C P N cauchyRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont E R cauchyRead ->
        Cont cauchyRead W sealRead ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row E ∨ hsame row R ∨ hsame row W ∨ hsame row cauchyRead ∨
                  hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont E R cauchyRead ∧ Cont cauchyRead W sealRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory cauchyRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier cauchyRoute sealRoute
  obtain ⟨_uUnary, _fUnary, eUnary, rUnary, wUnary, _dUnary, _sUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sourceRoute, _readbackRoute, _sealCarrierRoute,
    provenancePkg, localNamePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed eUnary rUnary cauchyRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed cauchyUnary wUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row R ∨ hsame row W ∨ hsame row cauchyRead ∨
              hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E R cauchyRead ∧ Cont cauchyRead W sealRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cauchyRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, cauchyUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
