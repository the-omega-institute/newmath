import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRealRegSeqRatL10Nonescape [AskSetup] [PackageSetup]
    {U F E R W D S H C P N dyadicRead streamRead regRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont D S dyadicRead ->
        Cont dyadicRead W streamRead ->
          Cont streamRead R regRead ->
            Cont regRead E realRead ->
              Cont realRead N namedRead ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                          hsame row E ∨ hsame row N ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D S dyadicRead ∧
                          Cont dyadicRead W streamRead ∧ Cont streamRead R regRead ∧
                            Cont regRead E realRead ∧ Cont realRead N namedRead ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory regRead ∧ UnaryHistory realRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier dyadicRoute streamRoute regRoute realRoute namedRoute namedPkg
  obtain ⟨_unaryU, _unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, _sourceRoute, _readbackRoute, _sealRoute,
      _provenancePkg, _localNamePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed unaryD unaryS dyadicRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary unaryW streamRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed streamUnary unaryR regRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regUnary unaryE realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S dyadicRead ∧ Cont dyadicRead W streamRead ∧
              Cont streamRead R regRead ∧ Cont regRead E realRead ∧
                Cont realRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, streamRoute, regRoute, realRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, regUnary, realUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
