import BEDC.Derived.CauchyCompletionMultiplicationUp.NameCertObligations

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMultiplicationRealSealNonescape [AskSetup] [PackageSetup]
    {M O I A S R D E H C P N flattenRead streamRead dyadicRead realRead structuralRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMultiplicationCarrier M O I A S R D E H C P N bundle pkg ->
      Cont M O flattenRead ->
        Cont S R streamRead ->
          Cont streamRead D dyadicRead ->
            Cont dyadicRead E realRead ->
              Cont realRead N structuralRead ->
                PkgSig bundle structuralRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                          hsame row structuralRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle structuralRead pkg)
                      hsame ∧
                    UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory realRead ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier _flattenRoute streamRoute dyadicRoute realRoute structuralRoute structuralPkg
  obtain ⟨_mUnary, _oUnary, _iUnary, _aUnary, sUnary, rUnary, dUnary, eUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _hM, _cP, _provenancePkg, _namePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary rUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary eUnary realRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed realUnary nUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
              hsame row structuralRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle structuralRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro structuralRead ⟨hsame_refl structuralRead, structuralUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, structuralPkg⟩
  }
  exact ⟨cert, streamUnary, dyadicUnary, realUnary, structuralUnary⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp
